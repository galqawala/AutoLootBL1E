"""AutoLootBL1E

A from-scratch port of the willow2_mods AutoLoot's feature set to Borderlands
GOTY Enhanced (BL1E). NOT a copy-paste: BL1E is Willow1, a different codebase
from BL2/TPS's Willow2, confirmed by reading BL1E's own decompiled class dump
(C:\\Users\\Omistaja\\bl1e_classes\\) and the game's own Localization/INT files
rather than assumed from the Willow2 source. Concretely different:

- No WillowGlobals.PickupList. Nearby pickups are found with
  unrealsdk.find_all("WillowPickup") + a manual distance filter instead - the
  same find_all pattern already used in this repo's AutoContainerMod and
  EnemyBalancer.
- No WillowPlayerController.PickupPickupable. Collecting an item is done by
  calling the pickup actor's own GiveTo(pawn, False) directly, the same call
  the third-party Autopickup SDK mod (willow1_all_mods\\Autopickup) already
  uses successfully in this exact game.
- No WillowPlayerController.bWantsToFire field. BL1E's StartFire/StopFire are
  exec functions like BL2/TPS's (confirmed in WillowPlayerController.uc) but
  set no flag a mod can read, so fire-held state is tracked here instead, by
  hooking StartFire/StopFire ourselves.
- No GetEmptyBackpackSlots(). Backpack fullness is derived from
  CountUnreadiedInventory() vs GetUnreadiedInventoryMaxSize(), both of which
  do exist under those exact names.
- BL1's item taxonomy is not BL2/TPS's. There are no WillowShield/
  WillowGrenadeMod/WillowArtifact/customization classes at all - shields,
  grenade mods and class mods are all the one WillowEquipAbleItem class,
  distinguished only by DefinitionData.ItemDefinition.EquipmentLocation
  (EQUIPLOC_Shield=0, EQUIPLOC_MOD=1 which is grenade mods, EQUIPLOC_Deck=2
  which is class mods - confirmed via ItemDefinition.uc's enum and
  WillowGame.int's `comm="CLASS MODS"` string). Artifacts and SDUs (Storage
  Deck Upgrades - backpack/ammo/weapon-slot capacity items) are both the one
  WillowUsableItem class instead, told apart only by which content package
  their ItemDefinition comes from (confirmed via the game's own
  Localization/INT/gd_ElementalUpgrade.INT and gd_StorageDeckUpgrade.INT):
  object paths under "gd_ElementalUpgrade." are artifacts, under
  "gd_StorageDeckUpgrade." are SDUs. There is no Oz Kit/Relic (that is BL2/
  TPS only) and no skin/head customization system in BL1E at all, so AutoLoot's
  corresponding options have nothing to port to and are simply absent here.
- "Using" an artifact or SDU from the backpack is the same
  ReadyBackpackInventory() call already used to equip a shield/mod/class mod -
  WillowUsableItem.Readied() (confirmed in WillowUsableItem.uc) calls
  ConsumeItem() on itself as part of being readied, so no separate
  TryConsume-style call is needed or exists under that name.

Known gaps, called out rather than silently guessed at: BL1E exposes no
PendingFire/GetPendingFireLength/ForceEndFire under those names, so unlike
AutoLoot this cannot detect or clear a weapon's still-pending fire mode
before switching off it - if BL1E has the same "switch while fire is pending
jams the new weapon" behaviour AutoLoot found in BL2/TPS, that protection is
not present here yet. Likewise PendingWeapon/InventoryTransitionInProgress/
IsPuttingDown (used to avoid interrupting an in-progress weapon swap) are
read defensively with getattr and silently no-op if absent, rather than
assumed present. The "My Class" filter for class mods/artifacts is a
best-effort match of the player's character name against the item
definition's own object name (e.g. "ElementalArtifact_Lilith") since no
PlayerClassRequirementMet-style function was found in the dump for BL1E -
this needs in-game confirmation.

This is a first port verified against static decompiled source, not against
actual play - unlike willow2_mods/AutoLoot, which reached its current design
through many rounds of real in-game testing. Treat it accordingly and watch
the SDK console log for [AutoLootBL1E] warnings while testing.
"""

import math
import random
import re

from mods_base import BoolOption, DropdownOption, SliderOption, build_mod, hook
from ui_utils import show_hud_message
from unrealsdk import logging
from unrealsdk.hooks import Block, Type
import unrealsdk

SCAN_INTERVAL = 20
FAST_SCAN_INTERVAL = 1
# An unresolved candidate (e.g. an item correctly declined for taking the
# last backpack slot) gets re-evaluated every tick for as long as it sits
# there - correct, since its surroundings could change at any tick - but
# re-logging the identical line every ~0.1s while nothing changes is pure
# spam. This only throttles which of those re-evaluations also produce a log
# line; every tick still runs the real decision.
LOG_REPEAT_COOLDOWN = 30.0

ticks_until_scan = 0
active_last_pass = False
next_near_loot_report = 0.0
last_shown_body = None
fire_held = False
picking_up = False
warned_remote_client = False
_recent_log_messages: dict[str, float] = {}


def log_throttled(now: float, message: str) -> None:
    """logging.info(message), but skipped if the exact same text was already
    logged within LOG_REPEAT_COOLDOWN seconds."""
    last = _recent_log_messages.get(message)
    if last is not None and now - last < LOG_REPEAT_COOLDOWN:
        return
    _recent_log_messages[message] = now
    logging.info(message)

pickup_weapons = BoolOption("Pickup Weapons", True)
pickup_shields = BoolOption("Pickup Shields", True)
pickup_grenade_mods = BoolOption("Pickup Grenade Mods", True)
pickup_sdus = BoolOption("Pickup SDUs", True, description="Storage Deck Upgrades.")

CHOICE_ALL = "All"
CHOICE_NONE = "None"
MY_CLASS_ONLY = "My class"

pickup_class_mods = DropdownOption(
    "Pickup Class Mods",
    MY_CLASS_ONLY,
    [CHOICE_ALL, MY_CLASS_ONLY, CHOICE_NONE],
    description=(
        "\"My class\" leaves behind class mods your character cannot equip."
        " Pick \"All\" if you collect them for your other characters."
    ),
)
pickup_artifacts = DropdownOption(
    "Pickup Artifacts",
    MY_CLASS_ONLY,
    [CHOICE_ALL, MY_CLASS_ONLY, CHOICE_NONE],
    description=(
        "\"My class\" leaves behind artifacts your character cannot use."
        " Pick \"All\" if you collect them for your other characters."
    ),
)
auto_use_artifacts = BoolOption(
    "Auto Use Artifacts",
    True,
    description="Use artifacts as soon as picked up, unlocking them for skill selection.",
)
auto_use_sdus = BoolOption(
    "Auto Use SDUs",
    True,
    description="Use Storage Deck Upgrades as soon as picked up - always beneficial.",
)
auto_use_healing_kit_at_health_percent = SliderOption(
    "Heal Kit At HP %",
    50,
    0,
    100,
    5,
    True,
    description=(
        "Use a carried Healing Kit from your backpack when your health drops"
        " to this % or below. 0 disables."
    ),
)
auto_equip = BoolOption(
    "Auto Equip",
    True,
    description="Fill empty shield/grenade mod/class mod/weapon slots automatically.",
)
switch_when_empty = BoolOption(
    "Switch When Out Of Ammo",
    True,
    description=(
        "When the gun in your hands runs dry, switch to the next equipped slot"
        " that still has ammo."
    ),
)
drop_lowest_when_full = BoolOption(
    "Drop Worst Item When Full",
    True,
    description=(
        "When full, drop whatever is worth least: an item over your level"
        " first, else the weakest one. Never a favourite."
    ),
)
range_percent = SliderOption(
    "Pickup Range %",
    100,
    25,
    500,
    25,
    True,
    description="How far AutoLootBL1E reaches, as % of your normal pickup range.",
)
hud_summary_seconds = SliderOption(
    "HUD Summary Seconds",
    19,
    0,
    60,
    1,
    True,
    description=(
        "Show what your backpack now holds on screen after clearing a pile of"
        " loot, for this many seconds. 0 disables the on-screen summary."
    ),
)
summary_in_console = BoolOption(
    "Console Summary",
    True,
    description="Write the same summary to the SDK console.",
)

# ItemDefinition.EEquipmentLoc values (ItemDefinition.uc): Shield=0, grenade
# MOD=1, class mod "Deck"=2. WillowUsableItem (artifacts/SDUs) has no
# EquipmentLocation that means anything - told apart by content package
# instead, see ARTIFACT_PACKAGE_PREFIX / SDU_PACKAGE_PREFIX below.
EQUIPLOC_SHIELD = 0
EQUIPLOC_GRENADE_MOD = 1
EQUIPLOC_CLASS_MOD = 2

# str(ItemDefinition_instance) renders as "ItemDefinition'package.group.object'"
# (the same ClassName'Package...' format AutoContainerMod's own TREASURE_
# PACKAGE_PREFIXES already includes the class name for) - these were missing
# that "ItemDefinition'" segment, so path.startswith() below never matched
# anything and item_kind() silently returned None for every artifact and SDU,
# for both pickup and auto-use, the whole time. Confirmed via BL1E's own
# Localization/INT/gd_StorageDeckUpgrade.INT (Backpack SDU's ItemDefinition
# is INV_InventorySpace.INV_InventorySpace in that package).
ARTIFACT_PACKAGE_PREFIX = "ItemDefinition'gd_ElementalUpgrade."
SDU_PACKAGE_PREFIX = "ItemDefinition'gd_StorageDeckUpgrade."

KIND_WEAPON = "Weapon"
KIND_SHIELD = "Shield"
KIND_GRENADE_MOD = "Grenade Mod"
KIND_CLASS_MOD = "Class Mod"
KIND_ARTIFACT = "Artifact"
KIND_SDU = "SDU"


def item_definition_of(inventory):
    definition_data = getattr(inventory, "DefinitionData", None)
    if definition_data is None:
        return None
    return getattr(definition_data, "ItemDefinition", None)


def item_definition_path(inventory) -> str:
    """The definition's `Class'package.Object'`-style path, or "" if unreadable.

    The same str(obj) pattern AutoContainerMod already uses to recognise which
    content package an object's definition comes from.
    """
    item_def = item_definition_of(inventory)
    if item_def is None:
        return ""
    try:
        return str(item_def)
    except Exception:  # noqa: BLE001
        return ""


def item_kind(inventory):
    """Which of our six tracked categories this pickup/backpack item is, or None."""
    if inventory is None or inventory.Class is None:
        return None
    class_name = inventory.Class.Name

    if class_name == "WillowWeapon":
        return KIND_WEAPON

    if class_name == "WillowUsableItem":
        path = item_definition_path(inventory)
        if path.startswith(ARTIFACT_PACKAGE_PREFIX):
            return KIND_ARTIFACT
        if path.startswith(SDU_PACKAGE_PREFIX):
            return KIND_SDU
        return None  # ammo/health/currency etc - not our concern

    if class_name == "WillowEquipAbleItem":
        item_def = item_definition_of(inventory)
        location = getattr(item_def, "EquipmentLocation", None)
        if location is None:
            return None
        location = int(location)
        if location == EQUIPLOC_SHIELD:
            return KIND_SHIELD
        if location == EQUIPLOC_GRENADE_MOD:
            return KIND_GRENADE_MOD
        if location == EQUIPLOC_CLASS_MOD:
            return KIND_CLASS_MOD
        return None

    return None


def prettify_ammo_name(name: str) -> str:
    name = str(name).removeprefix("Ammo_").replace("_", " ")
    return re.sub(r"(?<=[a-z])(?=[A-Z])", " ", name)


def ammo_label(weapon) -> str:
    """Which ammo pool this weapon draws from, e.g. "Combat Rifle"."""
    weapon_type = weapon.DefinitionData.WeaponTypeDefinition
    resource = None if weapon_type is None else weapon_type.AmmoResource
    if resource is None:
        return "Other Weapons"
    return prettify_ammo_name(resource.Name)


def comparison_group(item):
    """A finer split of item_kind(), used only for "what's this competing
    against" (choose_worst_item) and the backpack summary - never for pickup
    filtering or equip-slot dispatch, which stay on the coarse item_kind().

    Without this, EVERY weapon competes against ALL other weapons regardless
    of type when deciding whether a new one is "worth taking" - confirmed in
    play: with 48 assorted weapons already in the backpack, new pickups
    almost always lost that comparison and nothing new was ever taken, even
    with plenty of backpack space free. Splitting weapons by ammo type (the
    same grouping AutoLoot uses in Willow2) means a new Combat Rifle only
    competes against other Combat Rifles already held, not against every
    weapon in the bag.
    """
    kind = item_kind(item)
    if kind == KIND_WEAPON:
        return ammo_label(item)
    return GEAR_LABELS.get(kind, kind)


def player_character_requirement(caller):
    """This player's class, expressed as the ECharacterRequirement value that
    matches it (CR_Roland=1 .. CR_Brick=4), or None if unreadable.

    This is real game data, not a guess: WillowItem.IsPlayerRestricted
    (confirmed present in the BL1E dump under that exact name - the same
    function AutoLoot's own Willow2 version already relies on) computes
    exactly this value via `WPC.PlayerClass.CharacterName + 1` before
    comparing it against the item's own
    DefinitionData.ItemDefinition.RequiredCharacter (GlobalsDefinition.uc:
    enum ECharacterRequirement { CR_None, CR_Roland, CR_Mordecai, CR_Lilith,
    CR_Brick }, offset by exactly one from CharacterNames { CN_Roland=0 .. }).
    IsPlayerRestricted itself is `protected`, so - consistent with this
    codebase's preference for plain attribute reads over native/protected
    calls wherever the same data is reachable that way - the mapping is
    replicated here as a field read instead of calling that function.
    """
    player_class = getattr(caller, "PlayerClass", None)
    if player_class is None:
        return None
    raw = getattr(player_class, "CharacterName", None)
    if raw is None:
        return None
    try:
        return int(raw) + 1
    except (TypeError, ValueError):
        return None


def is_for_my_class(inventory, caller) -> bool:
    """Whether this class mod/artifact's class restriction (if any) matches
    the player's own class - real data (ItemDefinition.RequiredCharacter),
    not a guess parsed from the item's own object name. RequiredCharacter is
    a field on the one ItemDefinition class every item shares, so this reads
    identically for both kinds.
    """
    item_def = item_definition_of(inventory)
    required = getattr(item_def, "RequiredCharacter", None) if item_def is not None else None
    if required is None:
        return True
    required = int(required)
    if required == 0:  # CR_None - no restriction
        return True
    mine = player_character_requirement(caller)
    if mine is None:
        return True
    return mine == required


PICKUP_FILTERS = (
    (pickup_weapons, KIND_WEAPON),
    (pickup_shields, KIND_SHIELD),
    (pickup_grenade_mods, KIND_GRENADE_MOD),
    (pickup_sdus, KIND_SDU),
)

# Class Mods and Artifacts share the same three-way All/My class/None choice
# and the same RequiredCharacter-based check - one table instead of two
# near-identical branches, so the two can never drift apart from each other.
CLASS_FILTERED_KINDS = (
    (KIND_CLASS_MOD, pickup_class_mods),
    (KIND_ARTIFACT, pickup_artifacts),
)


def should_pickup(inventory, caller) -> bool:
    kind = item_kind(inventory)
    if kind is None:
        return False

    for filtered_kind, option in CLASS_FILTERED_KINDS:
        if kind != filtered_kind:
            continue
        if option.value == CHOICE_NONE:
            return False
        if option.value == CHOICE_ALL:
            return True
        return is_for_my_class(inventory, caller)

    return any(option.value and kind == token for option, token in PICKUP_FILTERS)


# WeaponDefinitionData/ItemDefinitionData (WillowWeaponTypes.uc/WillowItemTypes.uc)
# field names - what actually distinguishes one specific roll from another.
WEAPON_SIGNATURE_FIELDS = (
    "WeaponTypeDefinition", "BalanceDefinition", "ManufacturerDefinition",
    "ManufacturerGradeIndex", "BodyPartDefinition", "GripPartDefinition",
    "MagazinePartDefinition", "BarrelPartDefinition", "SightPartDefinition",
    "StockPartDefinition", "ActionPartDefinition", "AccessoryPartDefinition",
    "MaterialPartDefinition", "PrefixPartDefinition", "TitlePartDefinition",
)
ITEM_SIGNATURE_FIELDS = (
    "ItemDefinition", "BalanceDefinition", "ManufacturerDefinition",
    "ManufacturerGradeIndex", "BodyItemPartDefinition", "LeftSideItemPartDefinition",
    "RightSideItemPartDefinition", "MaterialItemPartDefinition",
    "PrefixItemNamePartDefinition", "TitleItemNamePartDefinition",
)


def item_composition_signature(inventory):
    """A tuple identifying this item's exact roll (manufacturer, parts,
    grade...) - the only real identity BL1E items have, since neither
    WeaponDefinitionData nor ItemDefinitionData has a UniqueId field at all
    (confirmed: grepping the entire class dump for "UniqueId" turns up only
    unrelated player network-identity fields, nowhere on WillowInventory or
    either DefinitionData struct). Composition is also what survives a BL1E
    throw, which true identity would not have anyway: ThrowBackpackInventory
    (WillowInventoryManager.uc) destroys the original item and has the server
    spawn a brand new WillowWeapon/WillowItem from a snapshot of these same
    fields (ServerThrowWeaponFromBackpack/ServerThrowItemFromBackpack).
    Confirmed in play before this was the sole identity mechanism: the mod
    picked its own just-dropped item straight back up, forcing another drop,
    repeating indefinitely (visible as the weapon flickering in place).
    """
    if inventory is None or inventory.Class is None:
        return None
    definition_data = getattr(inventory, "DefinitionData", None)
    if definition_data is None:
        return None
    class_name = inventory.Class.Name
    fields = WEAPON_SIGNATURE_FIELDS if class_name == "WillowWeapon" else ITEM_SIGNATURE_FIELDS
    return (class_name, *(getattr(definition_data, field, None) for field in fields))


# Permanent for the whole session, not a cooldown - the only "already seen"
# identity BL1E items have (see item_composition_signature for why there is
# no true UniqueId to fall back on). Once something has been owned - equipped,
# in the backpack, or dropped, auto or manual - it must never be picked up
# again this session. This is also what stops a duplicate of something
# currently equipped from being picked up: its signature is recorded every
# scan same as anything else owned, so a match is already excluded without
# any separate check.
seen_signatures = set()


def remember_signature(inventory):
    signature = item_composition_signature(inventory)
    if signature is not None:
        seen_signatures.add(signature)


def signature_already_seen(inventory) -> bool:
    signature = item_composition_signature(inventory)
    return signature is not None and signature in seen_signatures


def iter_owned_inventory(caller):
    """Every item the player holds - backpack first, then what is equipped.

    Was only walking InventoryChain (the weapon chain) - WillowInventoryManager.uc
    also declares a separate ItemChain (confirmed: `var Inventory ItemChain;`),
    the same weapon-chain/item-chain split AutoLoot's Willow2 version walks
    both of. Missing it meant an equipped shield, grenade mod or class mod was
    never recorded as owned by update_seen_ids at all.
    """
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager:
        yield from inventory_manager.Backpack

    pawn = caller.Pawn
    if pawn is None or pawn.InvManager is None:
        return
    for chain in (
        getattr(pawn.InvManager, "InventoryChain", None),
        getattr(pawn.InvManager, "ItemChain", None),
    ):
        item = chain
        while item is not None:
            yield item
            item = getattr(item, "Inventory", None)


def update_seen_ids(caller):
    for item in iter_owned_inventory(caller):
        remember_signature(item)


def use_backpack_extras(caller):
    """Auto-use backpack artifacts/SDUs via the same call that equips gear.

    WillowUsableItem.Readied() consumes the item itself (ConsumeItem()) as
    part of being readied - confirmed in WillowUsableItem.uc - so there is no
    separate consume call to make here, just the ordinary equip-from-backpack
    call already used for shields/mods below.
    """
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return

    for item in list(inventory_manager.Backpack):
        try:
            kind = item_kind(item)
            if kind not in (KIND_ARTIFACT, KIND_SDU):
                continue
            if kind == KIND_ARTIFACT and not auto_use_artifacts.value:
                logging.info(f"[AutoLootBL1E] not auto-using {comparison_group(item)} - option is off")
                continue
            if kind == KIND_SDU and not auto_use_sdus.value:
                logging.info(f"[AutoLootBL1E] not auto-using {comparison_group(item)} - option is off")
                continue
            inventory_manager.ReadyBackpackInventory(item)
            still_present = item in inventory_manager.Backpack
            logging.info(
                f"[AutoLootBL1E] auto-use {comparison_group(item)}:"
                f" ReadyBackpackInventory called, still_in_backpack={still_present}"
            )
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] could not use {item_kind(item)}: {ex!r}")


# "Healing Kit" tiers (HealthPack_1..5) - a carryable backpack item, distinct
# from the small instant-consume "Insta-Health Vial" pickups (HealthVial_1..5,
# which are never routed through here at all and never sit in the backpack -
# see AutopickupBL1E, which already picks both families up on the ground).
# Confirmed in gd_HealthDrops.INT: "Can be carried in your Storage Deck."
# Deliberately NOT wired into item_kind()/KIND_* - a Healing Kit should never
# become a drop-when-full candidate or participate in the worst-item
# comparison; the player is keeping it as an emergency reserve, not loot to
# manage.
HEALTH_KIT_NAMES = frozenset((
    "HealthPack_1",
    "HealthPack_2",
    "HealthPack_3",
    "HealthPack_4",
    "HealthPack_5",
))


def is_health_kit(item) -> bool:
    if item is None or item.Class is None or item.Class.Name != "WillowUsableItem":
        return False
    item_def = item_definition_of(item)
    return item_def is not None and str(item_def.Name) in HEALTH_KIT_NAMES


def maybe_use_healing_kit(caller):
    """Use one carried Healing Kit when health drops to the configured % or below.

    0 disables - one control expressing off, rather than a separate enable
    checkbox, per this codebase's own convention.

    GetHealth()/GetMaxHealth() are native Engine.Pawn functions the game's
    own HUD calls every frame for the health bar - about as safe a native
    call as exists in this engine, unlike the rarer ones elsewhere in this
    file that get extra caution and comments.
    """
    threshold = auto_use_healing_kit_at_health_percent.value
    if threshold <= 0:
        return

    pawn = caller.Pawn
    if pawn is None:
        return
    try:
        health = pawn.GetHealth()
        max_health = pawn.GetMaxHealth()
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not read health: {ex!r}")
        return
    if max_health <= 0 or health >= max_health:
        # No point healing at full health regardless of the threshold - this
        # also stops threshold=100 (the slider's own max) from firing on
        # every single scan forever, since health is always <=100% of itself.
        return
    if (health / max_health * 100) > threshold:
        return

    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return

    for item in list(inventory_manager.Backpack):
        if not is_health_kit(item):
            continue
        try:
            inventory_manager.ReadyBackpackInventory(item)
            logging.info(
                f"[AutoLootBL1E] auto-used a Healing Kit at"
                f" {health:.0f}/{max_health:.0f} health ({threshold}% threshold)"
            )
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] could not auto-use Healing Kit: {ex!r}")
        return  # one at a time - re-check health next scan before using another


WEAPON_SLOTS = (1, 2, 3, 4)


def has_ammo(weapon) -> bool:
    return bool(weapon.HasAnyAmmo())


def weapon_swap_in_progress(caller) -> bool:
    """Best-effort in-progress-swap check.

    Willow2's PendingWeapon/InventoryTransitionInProgress/IsPuttingDown were
    not confirmed present under these names in the BL1E dump - read
    defensively and default to "not in progress" (False) when absent, since
    that is the same as AutoLoot's own behaviour before it discovered and
    added this exact check. If BL1E turns out to have the same interrupted-
    swap jamming bug AutoLoot found in BL2/TPS, this will not yet catch it.
    """
    pawn = caller.Pawn
    if pawn is None or pawn.InvManager is None:
        return False
    manager = pawn.InvManager
    pending = getattr(manager, "PendingWeapon", None)
    if pending is not None:
        return True
    transition_check = getattr(manager, "InventoryTransitionInProgress", None)
    if callable(transition_check):
        try:
            if bool(transition_check()):
                return True
        except Exception:  # noqa: BLE001
            pass
    weapon = pawn.Weapon
    if weapon is not None:
        putting_down = getattr(weapon, "IsPuttingDown", None)
        if callable(putting_down):
            try:
                return bool(putting_down())
            except Exception:  # noqa: BLE001
                return False
    return False


def equipped_weapons(caller):
    pawn = caller.Pawn
    if pawn is None or pawn.InvManager is None:
        return {}
    by_slot = {}
    weapon = getattr(pawn.InvManager, "InventoryChain", None)
    while weapon is not None:
        slot = int(getattr(weapon, "QuickSelectSlot", 0))
        if slot in WEAPON_SLOTS:
            by_slot[slot] = weapon
        weapon = getattr(weapon, "Inventory", None)
    return by_slot


def next_loaded_slot(current, by_slot):
    for offset in range(1, len(WEAPON_SLOTS)):
        slot = (current - 1 + offset) % len(WEAPON_SLOTS) + 1
        weapon = by_slot.get(slot)
        if weapon is not None and has_ammo(weapon):
            return slot
    return None


def player_has_ammo_for(caller, weapon) -> bool:
    """Whether the player is carrying ammo of this weapon's type.

    HasAnyAmmo is only meaningful for a weapon that is actually equipped - a
    backpack weapon has no ammo pool attached to answer it correctly (same
    reasoning as AutoLoot's Willow2 version). GetResourcePoolForResourceDefinition
    is confirmed present under this name in the BL1E dump.

    Anything that cannot be determined counts as having ammo, so an
    unfamiliar weapon still gets offered as a backup rather than silently
    passed over.
    """
    weapon_type = weapon.DefinitionData.WeaponTypeDefinition
    resource = None if weapon_type is None else weapon_type.AmmoResource
    if resource is None:
        return True  # nothing to run out of
    pool = caller.GetResourcePoolForResourceDefinition(resource, False)
    data = None if pool is None else pool.Data
    if data is None:
        return True
    return data.GetCurrentValue() > 0


def loaded_backpack_weapons(caller, inventory_manager):
    """Every backpack weapon the player is carrying ammo for."""
    return [
        item
        for item in inventory_manager.Backpack
        if item is not None
        and item.Class is not None
        and item.Class.Name == "WillowWeapon"
        and player_has_ammo_for(caller, item)
    ]


def weapon_signature(weapon):
    """Which ammo pool this weapon draws from - used to spread backup slots
    across different ammo types instead of refilling every dry slot with the
    same kind of gun.

    No elemental component, unlike AutoLoot's Willow2 version: BL1E's
    WeaponDefinitionData has no ElementalPartDefinition field at all
    (confirmed in WillowWeaponTypes.uc) - BL1's elemental weapons are not
    represented as a dedicated weapon part the way BL2/TPS's are, and there is
    nothing else safe (no native calls) to read for this without further
    investigation. Ammo type alone is still a meaningful signature.
    """
    weapon_type = weapon.DefinitionData.WeaponTypeDefinition
    return None if weapon_type is None else weapon_type.AmmoResource


def choose_backup_slot_weapon(caller, inventory_manager, avoid_signatures):
    """A random loaded backpack weapon, preferring one unlike what's already equipped."""
    loaded = loaded_backpack_weapons(caller, inventory_manager)
    if not loaded:
        return None
    fresh = [item for item in loaded if weapon_signature(item) not in avoid_signatures]
    return random.choice(fresh or loaded)


def refill_dry_backup_slots(caller):
    """Swap a dry weapon in any slot but the active one for a loaded backpack one.

    Never touches the active slot - see the comment above first_empty_weapon_slot
    in the Willow2 AutoLoot for why readying a backpack weapon into the
    CURRENT slot is a different, more careful operation than this one.
    """
    if not auto_equip.value:
        return
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return

    pawn = caller.Pawn
    current = None if pawn is None else pawn.Weapon
    current_slot = None if current is None else int(getattr(current, "QuickSelectSlot", 0))

    by_slot = equipped_weapons(caller)
    signatures = {slot: weapon_signature(weapon) for slot, weapon in by_slot.items()}

    for slot, weapon in by_slot.items():
        if slot == current_slot or has_ammo(weapon):
            continue
        try:
            avoid = {sig for other_slot, sig in signatures.items() if other_slot != slot}
            chosen = choose_backup_slot_weapon(caller, inventory_manager, avoid)
            if chosen is None:
                continue
            inventory_manager.ReadyBackpackInventory(chosen, slot)
            signatures[slot] = weapon_signature(chosen)
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] could not refill backup slot {slot}: {ex!r}")


def diversify_equipped_elements(caller):
    """Swap one of a pair of equipped weapons sharing an element for a fresh one.

    Ported from willow2_mods/AutoLoot (this was meant to already be part of
    this port - it was missed). Same algorithm, unchanged: non-elemental
    counts as its own element here - item_element already returns the same
    None for every non-elemental weapon, so two plain weapons equipped
    together count as "sharing an element" exactly like two Fire weapons
    would, with no special-casing needed. Never touches the active slot, for
    the same reason refill_dry_backup_slots does not.

    Only difference from the Willow2 version: the log message uses
    comparison_group() instead of item_kind() for the weapon type name -
    BL1E's item_kind() means something else entirely here (shield/mod/
    artifact/SDU classification, see item_kind's own docstring), and
    comparison_group() is this port's equivalent of what Willow2's item_kind
    already returns for weapons (an ammo/type label like "Sniper Rifle").
    """
    if not auto_equip.value:
        return

    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return

    pawn = caller.Pawn
    current = None if pawn is None else pawn.Weapon
    current_slot = None if current is None else int(getattr(current, "QuickSelectSlot", 0))

    by_slot = equipped_weapons(caller)
    elements = {slot: item_element(weapon) for slot, weapon in by_slot.items()}
    by_element = {}
    for slot, element in elements.items():
        by_element.setdefault(element, []).append(slot)

    for slots in by_element.values():
        if len(slots) < 2:
            continue
        replaceable = [slot for slot in slots if slot != current_slot]
        if not replaceable:
            continue
        # Random rather than always the same slot in the pair, so which one
        # gets swapped is not permanently biased toward e.g. the lowest slot
        # number.
        slot = random.choice(replaceable)
        try:
            other_elements = {e for s, e in elements.items() if s != slot}
            fresh = [
                item
                for item in loaded_backpack_weapons(caller, inventory_manager)
                if item_element(item) not in other_elements
            ]
            if not fresh:
                continue
            chosen = random.choice(fresh)
            old_group = comparison_group(by_slot[slot])
            inventory_manager.ReadyBackpackInventory(chosen, slot)
            logging.warning(
                f"[AutoLootBL1E] slot {slot}: {old_group} -> {comparison_group(chosen)},"
                " no longer sharing an element with another slot"
            )
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] could not diversify slot {slot}: {ex!r}")


def manage_weapon_ammo(caller):
    """Switch off a dry weapon onto an equipped, loaded one.

    Unlike AutoLoot, this cannot clear a still-pending fire mode first (no
    ForceEndFire/PendingFire found in the BL1E dump) - if switching off a dry
    weapon while still "firing" jams the new one the way it did in BL2/TPS
    before that was discovered, this will reproduce that bug. Watch for it.
    """
    if not switch_when_empty.value:
        return
    if weapon_swap_in_progress(caller):
        return

    pawn = caller.Pawn
    current = None if pawn is None else pawn.Weapon
    if current is None or has_ammo(current):
        return

    current_slot = int(getattr(current, "QuickSelectSlot", 0))
    if current_slot not in WEAPON_SLOTS:
        return

    by_slot = equipped_weapons(caller)
    loaded_slot = next_loaded_slot(current_slot, by_slot)
    if loaded_slot is None:
        return

    if fire_held:
        # No way to force-clear pending fire here - postpone rather than risk
        # jamming the weapon by switching mid-trigger-hold.
        return

    logging.info(f"[AutoLootBL1E] slot {current_slot} -> {loaded_slot}")
    caller.EquipWeaponFromSlot(loaded_slot)


def first_empty_weapon_slot(caller, inventory_manager):
    """The lowest unlocked quick slot with no weapon in it, or None.

    GetWeaponInSlot does not exist on BL1E's WillowInventoryManager (confirmed
    via unrealsdk.log: every call threw AttributeError, silently swallowed by
    the caller's try/except - weapons were never being auto-equipped as a
    result). Uses the same InventoryChain walk equipped_weapons() already
    relies on elsewhere instead of a slot-lookup call.
    """
    unlocked = min(int(inventory_manager.GetWeaponReadyMax()), len(WEAPON_SLOTS))
    by_slot = equipped_weapons(caller)
    for slot in WEAPON_SLOTS[:unlocked]:
        if slot not in by_slot:
            return slot
    return None


# ItemDefinition.EEquipmentLoc value -> WillowPawn.EquippedItems index. Same
# enum, same array - WillowPawn.uc declares `EquippedItems[3]` and indexes it
# with `EquippedItems[int(ItemDef.EquipmentLocation)]` throughout.
EQUIP_SLOT_BY_KIND = {
    KIND_SHIELD: EQUIPLOC_SHIELD,
    KIND_GRENADE_MOD: EQUIPLOC_GRENADE_MOD,
    KIND_CLASS_MOD: EQUIPLOC_CLASS_MOD,
}


def gear_slot_is_empty(caller, kind) -> bool:
    """Whether the EquippedItems[] slot this item's kind belongs to is free.

    Without this, ReadyBackpackInventory(item) would replace whatever is
    already equipped there every scan - confirmed in play: shields and
    grenade mods were being swapped for a random backpack one continuously,
    because this gate was missing entirely in the first cut of this port.
    """
    pawn = caller.Pawn
    if pawn is None:
        return False
    equipped = getattr(pawn, "EquippedItems", None)
    if equipped is None:
        return False
    location = EQUIP_SLOT_BY_KIND.get(kind)
    if location is None:
        return False
    try:
        return equipped[location] is None
    except Exception:  # noqa: BLE001
        return False


def is_worth_equipping(caller, item) -> bool:
    if item is None or item.Class is None:
        return False
    kind = item_kind(item)
    if kind == KIND_WEAPON:
        return True
    if kind in EQUIP_SLOT_BY_KIND:
        return gear_slot_is_empty(caller, kind)
    return False


def fill_empty_equip_slots(caller):
    if not auto_equip.value:
        return
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return

    candidates = [item for item in inventory_manager.Backpack if is_worth_equipping(caller, item)]
    random.shuffle(candidates)

    for item in candidates:
        try:
            kind = item_kind(item)
            if kind == KIND_WEAPON:
                slot = first_empty_weapon_slot(caller, inventory_manager)
                if slot is None:
                    continue
                inventory_manager.ReadyBackpackInventory(item, slot)
            else:
                # Re-check immediately before acting: an earlier item in this
                # same pass may have just filled this exact slot.
                if not gear_slot_is_empty(caller, kind):
                    continue
                inventory_manager.ReadyBackpackInventory(item)
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] could not equip from the backpack: {ex!r}")


def dist(a, b) -> float:
    return math.sqrt((b.X - a.X) ** 2 + (b.Y - a.Y) ** 2 + (b.Z - a.Z) ** 2)


SUMMARY_SEPARATOR = " | "

GEAR_LABELS = {
    KIND_WEAPON: "Weapons",
    KIND_SHIELD: "Shields",
    KIND_GRENADE_MOD: "Grenade Mods",
    KIND_CLASS_MOD: "Class Mods",
    KIND_ARTIFACT: "Artifacts",
    KIND_SDU: "SDUs",
}


def item_level(item, caller):
    """The item's level requirement as shown on its card, or None if unreadable.

    Reads GetControllerPlayerExpLevelRequiredToUse(caller) - a plain
    (non-native) function on the base WillowInventory class, so it applies
    identically to weapons and items - rather than the raw ExpLevel field.
    ExpLevel alone runs 1-2 levels above the displayed "Level Requirement"
    (the function adds a manufacturer-specific PlayerUseLevelBonus on top),
    so comparing raw ExpLevel against character level could mis-classify an
    item as over-level/usable relative to what the player actually sees on
    screen. This is the exact same calculation the item card's own text uses.

    Earlier history: this used to read DefinitionData.GameStage (wrong field
    entirely - GameStage's native accessor returned 0 for real backpack
    items), then raw ExpLevel (right field, but off by the manufacturer
    bonus from what's displayed). Both silently made the over-level split and
    the "furthest from level" step fail to discriminate correctly.
    """
    if item is None or item.Class is None:
        return None
    try:
        level = int(item.GetControllerPlayerExpLevelRequiredToUse(caller))
    except Exception as ex:  # noqa: BLE001
        # Kept as a caught warning, not an assert: unlike RarityLevel below,
        # there is no independent confirmation this call can never legitimately
        # fail for every item in every lifecycle state (e.g. mid-destroy), so
        # this is the "genuinely uncertain edge case" bucket, not the
        # "platform's own data model doesn't have this" bucket.
        logging.warning(f"[AutoLootBL1E] GetControllerPlayerExpLevelRequiredToUse failed: {ex!r}")
        return None
    # The function's own body ends with `rslt = Max(rslt, 1)` (confirmed in
    # WillowInventory.uc) - a successful call can never return <= 0, so
    # reaching this is not a legitimate "no level" case to quietly pass
    # through as None.
    assert level > 0, f"GetControllerPlayerExpLevelRequiredToUse returned {level}"
    return level


def character_level(caller):
    info = caller.PlayerReplicationInfo
    if info is None:
        return None
    level = int(info.ExpLevel)
    return level if level > 0 else None


def item_price(item, caller) -> int:
    """This item's sell value, i.e. GetSellingPriceForInventory(item).

    Not a method on the item itself - BL1E has no GetMonetaryValue anywhere
    (confirmed absent from the whole class dump; this was carried over from
    AutoLoot's Willow2 source without being checked against BL1E's own
    classes and failed on every single call). The real function is declared
    natively on WillowPawn (WillowPawn.uc), taking the item as an argument -
    the same call the inventory screen's own sell-value display uses.
    """
    pawn = caller.Pawn
    if pawn is None:
        return 0
    try:
        return int(pawn.GetSellingPriceForInventory(item))
    except Exception as ex:  # noqa: BLE001
        # Falling back to 0 makes this item look free, i.e. the cheapest
        # possible candidate - worth knowing about since that would bias it
        # straight to the front of the "worst item" comparison every time.
        logging.warning(f"[AutoLootBL1E] GetSellingPriceForInventory failed on {comparison_group(item)}: {ex!r}")
        return 0


def item_element(item):
    """This weapon's damage type (Fire, Corrosive, ...), or None for no element.

    Only weapons carry elemental data in BL1E, and only via the accessory
    part slot - confirmed in WillowWeapon.uc, whose own PickupWeaponEvent
    handler switches on exactly this field (DefinitionData.AccessoryPartDefinition
    .CustomDamageTypeDefinition.DamageType) to count elemental pickup stats
    (STAT_PLAYER_SHOCK_WEAPONS_PICKED_UP etc) - so this is the game's own
    read of a weapon's element, not a guess. Non-weapon items have no
    equivalent field on their ItemDefinitionData at all (no AccessoryPartDefinition
    there), matching AutoLoot's own Willow2 behaviour where item_element is
    also weapon-only and every non-weapon item groups together as "no
    element" - this is a fact about what data each item type carries, not
    special-case logic that treats weapons and items differently.
    """
    if item is None or item.Class is None or item.Class.Name != "WillowWeapon":
        return None
    part = getattr(item.DefinitionData, "AccessoryPartDefinition", None)
    if part is None:
        return None
    damage_type = getattr(getattr(part, "CustomDamageTypeDefinition", None), "DamageType", None)
    if damage_type is None:
        return None
    try:
        return int(damage_type)
    except Exception:  # noqa: BLE001
        return damage_type


# --- GearScore ---------------------------------------------------------
# Ported from eeriegoesd's GearScore mod
# (https://bl-sdk.github.io/willow1-mod-db/mods/gearscore/, GPL-3.0-or-later)
# to rank a group of same-kind, same-level-bracket, same-element candidates
# by quality, replacing a plain rarity-tier comparison. Credit: eeriegoesd,
# https://eeriegoesd.com/gaming/mods/.
#
# Two deliberate differences from the original, both because this score is
# computed on every drop-decision scan rather than only when a UI card is
# open, which is the GearScore mod's own only trigger:
#   1. Element is read via item_element() (a plain attribute chain already
#      proven working elsewhere in this file) instead of GearScore's own
#      read_element(), which calls the native StaticGetWeaponDamageType -
#      avoids one native call entirely, per this codebase's own preference
#      for a plain attribute read over a native call wherever one exists.
#   2. Accuracy and critical-hit bonus are always disregarded (GearScore's
#      own defaults) since there is no item-card UI here to read them from.
#
# Everything else, including GearScore's one remaining native call -
# StaticCalculateWeaponTechLevelForUI, for a backpack weapon's elemental proc
# level, which has no plain-attribute equivalent (TechLevel itself only
# reflects the currently EQUIPPED weapon's live tech pool) - is a faithful,
# unchanged port. GearScore already calls this same function across many
# backpack weapons at once, in this same game, in its own published DPS-sort
# backpack page - the closest thing to in-game verification available without
# running the game directly, but still worth watching if a crash is ever seen
# near a drop decision.

# Elements measured against plain flesh, the surface with no resistance
# either way - matches GearScore's own FLESH_SURFACE assumption. Keyed by
# item_element()'s own DamageType ints (WillowDamageTypeDefinition.EDamageType)
# rather than GearScore's element-name strings.
GEARSCORE_ELEMENT_SPLASH = {
    1: 0.6,  # Incindiary
    2: 1.0,  # Shock
    3: 1.5,  # Explosive
    4: 0.4,  # Corrosive
}

# What the game calls each sort of gun, and what the cheapest elemental
# splash costs from its tech pool / how hard it hits - both straight from
# GearScore's own FAMILY_NAMES/PROC_TABLE.
GEARSCORE_FAMILY_NAMES = {
    "repeater": ("repeater", "machine_pistol"),
    "revolver": ("revolver",),
    "smg": ("smg",),
    "shotgun": ("shotgun",),
    "rifle": ("combat_rifle",),
    "sniper": ("sniper",),
}
GEARSCORE_PROC_TABLE = {
    "repeater": (4.0, 1.0),
    "revolver": (0.0, 1.0),
    "smg": (12.0, 1.0),
    "shotgun": (20.0, 1.0),
    "rifle": (20.0, 1.0),
    "sniper": (32.0, 1.0),
}
GEARSCORE_POOL_REFILL = 4.0  # How fast the tech pool refills, same for every gun.

# Seconds of fighting the shield score is measured over - GearScore's own
# SHIELD_WINDOW.
GEARSCORE_SHIELD_WINDOW = 60.0

GEARSCORE_SHIELD_DEFINITION = "gd_shields.A_Item.Item_Shield"
GEARSCORE_DELAY_ATTRIBUTE = "d_attributes.ShieldResourcePool.ShieldOnIdleRegenerationDelay"
_gearscore_shield_delay_patched = False


def _patch_gearscore_shield_delay() -> None:
    """One-time patch so a shield's recharge DELAY is readable at all.

    Shields only expose capacity and recharge RATE through their normal
    UIStats slot list - the delay needs its own attribute wired into a spare
    slot first, same as GearScore's own patch_shield_delay(). Idempotent and
    global (patches the shared ItemDefinition once, not per-item), the same
    ObjectFlags|=0x4000 definition-patch pattern the original BL1 Autopickup
    SDK mod already used successfully in this exact game.
    """
    global _gearscore_shield_delay_patched
    if _gearscore_shield_delay_patched:
        return
    try:
        unrealsdk.load_package(GEARSCORE_SHIELD_DEFINITION)
        definition = unrealsdk.find_object("ItemDefinition", GEARSCORE_SHIELD_DEFINITION)
        attribute = unrealsdk.find_object("ResourcePoolAttributeDefinition", GEARSCORE_DELAY_ATTRIBUTE)
        definition.ObjectFlags |= 0x4000
        definition.UIStats[2].Attribute = attribute
        _gearscore_shield_delay_patched = True
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not expose shield recharge delay for scoring: {ex!r}")


def _gearscore_read(item, name: str, fallback: float) -> float:
    value = getattr(item, name, None)
    if value is None or not isinstance(value, (int, float)) or isinstance(value, bool):
        return fallback
    return float(value)


def _gearscore_family(weapon) -> str | None:
    try:
        kind = str(weapon.DefinitionData.WeaponTypeDefinition.Name).lower()
    except Exception:  # noqa: BLE001
        return None
    for family, needles in GEARSCORE_FAMILY_NAMES.items():
        for needle in needles:
            if needle in kind:
                return family
    return None


def _gearscore_proc_level(weapon) -> int:
    """The x1 to x4 elemental splash rating GearScore reads off the card."""
    try:
        level = int(weapon.StaticCalculateWeaponTechLevelForUI(weapon.DefinitionData)[0])
    except Exception:  # noqa: BLE001
        return 1
    return min(max(level, 1), 4)


def _gearscore_element_dps(weapon, shots_per_second: float) -> float:
    element = item_element(weapon)
    family = _gearscore_family(weapon)
    if element not in GEARSCORE_ELEMENT_SPLASH or family is None:
        return 0.0

    cost, proc_multiplier = GEARSCORE_PROC_TABLE[family]
    damage = _gearscore_read(weapon, "InstantHitDamage", 0)
    level = _gearscore_proc_level(weapon)

    procs = shots_per_second if cost <= 0 else min(GEARSCORE_POOL_REFILL / cost, shots_per_second)
    return procs * damage * GEARSCORE_ELEMENT_SPLASH[element] * proc_multiplier * level


def _gearscore_dps(weapon) -> float | None:
    """Damage per second over a full magazine, including the reload after it."""
    damage = _gearscore_read(weapon, "InstantHitDamage", 0)
    projectiles = _gearscore_read(weapon, "ProjectilesPerShot", 1)
    fire_interval = _gearscore_read(weapon, "FireInterval", 0)
    clip_size = _gearscore_read(weapon, "ClipSize", 0)
    shot_cost = _gearscore_read(weapon, "ShotCost", 1)
    reload_time = _gearscore_read(weapon, "ReloadTime", 0)

    if damage <= 0 or fire_interval <= 0:
        return None

    shot_damage = damage * max(projectiles, 1)
    shots = clip_size / max(shot_cost, 1)

    if shots < 1:
        span = fire_interval
    else:
        burst = _gearscore_read(weapon, "AutomaticBurstCount", 0)
        pauses = 0.0 if burst <= 0 else -(-shots // burst) * fire_interval
        span = shots * fire_interval + pauses + reload_time

    rounds = max(shots, 1)
    bullets = rounds * shot_damage / span
    return bullets + _gearscore_element_dps(weapon, rounds / span)


def _gearscore_ui_stats(item) -> dict[str, float]:
    """Shields keep their numbers in a list rather than plain properties."""
    stats: dict[str, float] = {}
    try:
        definition = item.DefinitionData.ItemDefinition
        for index, modifier in enumerate(item.UIStatModifiers):
            name = str(definition.UIStats[index].Attribute).rsplit(".", 1)[-1].rstrip("'")
            stats[name] = float(modifier.ModifierTotal)
    except Exception:  # noqa: BLE001
        return stats
    return stats


def _gearscore_shield_score(item) -> float | None:
    """Damage a shield soaks over a minute: its capacity plus everything it recharges."""
    _patch_gearscore_shield_delay()
    stats = _gearscore_ui_stats(item)
    capacity = stats.get("ShieldMaxValue")
    rate = stats.get("ShieldOnIdleRegenerationRate")
    if capacity is None or rate is None:
        return None
    delay = stats.get("ShieldOnIdleRegenerationDelay", 0.0)
    return capacity + rate * max(GEARSCORE_SHIELD_WINDOW - delay, 0)


def item_gearscore(item) -> float:
    """How good a thing is - the WORST (lowest score) is the one to drop.

    Weapons score by expected DPS, shields by how much damage they soak in a
    minute, everything else (grenade mods, class mods, artifacts, SDUs)
    scores 0.0 - GearScore does not rate those either, so this step provides
    no differentiation for them and the funnel falls through to the price
    tiebreak below, same as a genuine tie would anywhere else in this chain.
    """
    kind = item_kind(item)
    if kind == KIND_WEAPON:
        score = _gearscore_dps(item)
        return 0.0 if score is None else score
    if kind == KIND_SHIELD:
        score = _gearscore_shield_score(item)
        return 0.0 if score is None else score
    return 0.0


def is_favorite(item) -> bool:
    """Always False - BL1E has no item-favoriting/marking system at all
    (confirmed absent from the dump: no PlayerMark field, no TF_Favorite,
    no SetMark/GetMark anywhere). item.GetMark() does not exist here; calling
    it threw AttributeError on every item, and the old code's fail-safe
    default (treat unreadable as favorited, to avoid ever auto-dropping
    something deliberately kept) meant EVERY item was silently treated as
    favorited - which is why droppable_backpack_items() always came back
    empty despite a full backpack. Kept as its own function, not inlined,
    so the call sites read the same as when this genuinely checked something."""
    return False


def backpack_is_full(caller) -> bool:
    """No GetEmptyBackpackSlots() in the BL1E dump - derived from the same
    two capacity numbers backpack_tally() already uses for the HUD summary
    (CountUnreadiedInventory/GetUnreadiedInventoryMaxSize alone - confirmed
    correct there, since it matches the game's own "Backpack N/54" display).

    This used to ALSO add CountReadiedWeapons() to the "used" side, which was
    wrong: "unreadied inventory" already means backpack-only, not counting
    equipped weapons at all, so adding readied weapon count on top over-
    counted by however many weapons were equipped (typically 4) and reported
    full a full 4 slots early - confirmed in play: dropped a weapon to make
    room while the HUD read Backpack 50/54, 4 slots free.
    """
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return False
    used = inventory_manager.CountUnreadiedInventory()
    return used >= inventory_manager.GetUnreadiedInventoryMaxSize()


def backpack_would_take_last_slot(caller) -> bool:
    """Whether picking up one more item would leave zero backpack slots free.

    Deliberately not the same thing as backpack_is_full() - this is one slot
    earlier, the moment BEFORE the backpack actually fills up, so the "would
    this become the next item to drop" check below can run while there's
    still exactly one open slot to lose, rather than only after it's gone.
    """
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return False
    used = inventory_manager.CountUnreadiedInventory()
    return used >= inventory_manager.GetUnreadiedInventoryMaxSize() - 1


def _tied_for_most(items, key_func):
    groups = {}
    for item in items:
        groups.setdefault(key_func(item), []).append(item)
    biggest = max(len(group) for group in groups.values())
    kept_labels = {label for label, group in groups.items() if len(group) == biggest}
    return [item for item in items if key_func(item) in kept_labels], groups


def _tied_for_extreme(items, key_func, pick_max):
    target = (max if pick_max else min)(key_func(item) for item in items)
    return [item for item in items if key_func(item) == target], target


def can_drop(item) -> bool:
    """Whether the game itself will let this specific item be dropped.

    caller.CanDrop(item) does not exist on WillowPlayerController in BL1E -
    the real check, CanInventoryBeDroppedByOwner(), is a no-arg method on the
    item itself (confirmed in Engine/WillowInventory.uc). Calling the wrong
    (nonexistent) function here would have thrown for every item too, on top
    of the separate is_favorite() bug above.
    """
    try:
        return bool(item.CanInventoryBeDroppedByOwner())
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] CanInventoryBeDroppedByOwner failed on {comparison_group(item)}: {ex!r}")
        return False


def droppable_backpack_items(caller):
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return []
    return [
        item
        for item in inventory_manager.Backpack
        if item_kind(item) is not None and not is_favorite(item) and can_drop(item)
    ]


def choose_worst_item(candidates, cap, caller, log=False, now=None):
    candidates = list(candidates)
    if not candidates:
        return None

    trace = []

    candidates, kind_groups = _tied_for_most(candidates, comparison_group)
    if log:
        sizes = {label: len(group) for label, group in kind_groups.items()}
        trace.append(f"kind {sizes}")

    if cap is not None and len(candidates) > 1:
        over_level = [item for item in candidates if (item_level(item, caller) or 0) > cap]
        usable = [item for item in candidates if (item_level(item, caller) or 0) <= cap]
        if over_level and usable:
            # Tied -> the overlevel (unusable) group, not usable - matches
            # step 4 below picking overlevel loot to drop over usable loot.
            candidates = over_level if len(over_level) >= len(usable) else usable
            if log:
                trace.append(f"over-level {len(over_level)} vs usable {len(usable)}")

    if len(candidates) > 1:
        candidates, element_groups = _tied_for_most(candidates, item_element)
        if log:
            sizes = {label: len(group) for label, group in element_groups.items()}
            trace.append(f"element {sizes}")

    # Only when every remaining candidate is actually unusable (over-level)
    # does dropping the HIGHEST level one make sense - it is the one that
    # takes longest to grow into. A usable group is left untouched here (no
    # filter at all - "include everything for potential drop") rather than
    # picking the one furthest from the character's level, which would have
    # dropped a low-level usable item just for being far below the cap.
    is_overlevel_group = cap is not None and all(
        (item_level(item, caller) or 0) > cap for item in candidates
    )
    if is_overlevel_group and len(candidates) > 1:
        candidates, level_value = _tied_for_extreme(
            candidates, lambda item: item_level(item, caller) or 0, pick_max=True
        )
        if log:
            trace.append(f"highest level, unusable ({level_value})")

    if len(candidates) > 1:
        candidates, score = _tied_for_extreme(
            candidates, item_gearscore, pick_max=False
        )
        if log:
            trace.append(f"gearscore {score:.1f}")

    if len(candidates) > 1:
        candidates, price = _tied_for_extreme(
            candidates, lambda item: item_price(item, caller), pick_max=False
        )
        if log:
            trace.append(f"price ${price}")

    # No real "lowest id" exists to break a final tie by (BL1E items have no
    # UniqueId at all - see item_composition_signature) - Python's own id()
    # is used purely as a stable, deterministic tiebreak for this one run,
    # not as anything meaningful about the item itself.
    chosen = min(candidates, key=id)
    if log:
        if len(candidates) > 1:
            trace.append("lowest id")
        message = (
            f"[AutoLootBL1E] drop: {comparison_group(chosen)} (lvl {item_level(chosen, caller)})"
            f" | {' -> '.join(trace)}"
        )
        log_throttled(now if now is not None else caller.WorldInfo.TimeSeconds, message)
    return chosen


def throw_backpack_item(caller, item) -> bool:
    # Recorded immediately, not just relying on the next update_seen_ids scan
    # to notice it's gone (see item_composition_signature for why composition
    # is the only identity BL1E throws preserve). Permanent, not a cooldown -
    # see seen_signatures.
    remember_signature(item)

    # Captured before the throw: ThrowBackpackInventory destroys the original
    # item synchronously (RemoveInventoryFromBackpack + Inv.Destroy(), per
    # WillowInventoryManager.uc), so reading anything off `item` afterwards
    # would be touching a possibly-destroyed object.
    kind_label = comparison_group(item)
    level = item_level(item, caller)

    inventory_manager = caller.GetPawnInventoryManager()
    count_before = len(inventory_manager.Backpack)
    inventory_manager.ThrowBackpackInventory(item)
    count_after = len(inventory_manager.Backpack)
    freed = count_after < count_before
    if freed:
        logging.warning(f"[AutoLootBL1E] dropped {kind_label} (lvl {level}) to make room")
    else:
        logging.warning(
            f"[AutoLootBL1E] tried to drop {kind_label} (lvl {level})"
            f" to free a backpack slot, but Backpack size stayed at {count_after}"
        )
    return freed


def backpack_tally(caller):
    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        return None

    counts = {}
    levels = {}
    for item in inventory_manager.Backpack:
        if item_kind(item) is None:
            continue
        label = comparison_group(item)
        counts[label] = counts.get(label, 0) + 1
        level = item_level(item, caller)
        if level is None:
            continue
        low, high = levels.get(label, (level, level))
        levels[label] = (min(low, level), max(high, level))

    return (
        counts,
        levels,
        inventory_manager.CountUnreadiedInventory(),
        inventory_manager.GetUnreadiedInventoryMaxSize(),
    )


def summary_line(counts, levels) -> str:
    ordered = sorted(counts.items(), key=lambda pair: (-pair[1], random.random()))
    parts = []
    for label, count in ordered:
        if not count:
            continue
        level_range = levels.get(label)
        if level_range is None:
            parts.append(f"{count} {label}")
            continue
        low, high = level_range
        span = f"lvl {low}" if low == high else f"lvl {low}-{high}"
        parts.append(f"{count} {label} ({span})")
    return SUMMARY_SEPARATOR.join(parts)


def format_tally(counts, levels, used, capacity):
    return f"Backpack  {used}/{capacity}", summary_line(counts, levels)


def report_backpack(caller):
    global last_shown_body
    if not (hud_summary_seconds.value or summary_in_console.value):
        return
    try:
        tally = backpack_tally(caller)
        if tally is None:
            return
        title, body = format_tally(*tally)
        if not body:
            return
        if summary_in_console.value:
            logging.info(f"{title}\n{body}")
        if hud_summary_seconds.value:
            if body == last_shown_body:
                return
            show_hud_message(title, body, hud_summary_seconds.value)
            last_shown_body = body
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not summarise the backpack: {ex!r}")


def nearby_pickups(view_location, max_dist):
    """Every live WillowPickup within range, as a plain list.

    unrealsdk.find_all is a global scan across the whole level, not a
    proximity search (same caveat documented in EnemyBalancer) - the distance
    filter here is what narrows it down, exactly mirroring how AutoLoot
    filtered willow_globals.PickupList by distance in Willow2.
    """
    try:
        candidates = list(unrealsdk.find_all("WillowPickup"))
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] find_all('WillowPickup') failed: {ex!r}")
        return []
    result = []
    for pickup in candidates:
        try:
            if pickup.Inventory is None:
                continue
            if not bool(getattr(pickup, "bPickupable", True)):
                continue
            if dist(pickup.Location, view_location) > max_dist:
                continue
        except Exception:  # noqa: BLE001
            continue
        result.append(pickup)
    return result


def attempt_pickup(caller, pickup) -> bool:
    """Try to collect one pickup. Returns whether the backpack grew.

    Deliberately does not read `pickup` again after GiveTo() - DroppedPickup.
    GiveTo (confirmed in the dump) does not appear to destroy the pickup
    actor synchronously, but success is judged from the backpack's own size
    instead of touching the pickup afterwards regardless, the same caution
    AutoLoot already applies to its own throw/drop calls.
    """
    global picking_up

    inventory_manager = caller.GetPawnInventoryManager()
    if inventory_manager is None:
        logging.warning(f"[AutoLootBL1E] no inventory manager, cannot pick up {comparison_group(pickup.Inventory)}")
        return False
    game = caller.WorldInfo.Game
    if game is None:
        # WorldInfo.Game is only ever populated on the server - confirmed in
        # WillowPlayerController.uc: the game's own pickup flow
        # (ServerPickupSomething/AllPlayersPickupQuery) is a `reliable server
        # function` specifically so its own PickupQuery call always runs
        # where Game is valid. On a remote multiplayer client (not the host)
        # Game is always None here, and this used to throw AttributeError on
        # every single pickup attempt - once per candidate per scan tick,
        # spamming the log. Auto-pickup only works for the host until this
        # has a real server-RPC path; logged once, not every tick, since
        # nothing about this changes tick to tick.
        global warned_remote_client
        if not warned_remote_client:
            warned_remote_client = True
            logging.warning(
                "[AutoLootBL1E] this player is a remote client, not the host -"
                " WorldInfo.Game is never available here, so auto-pickup/drop"
                " cannot run. Manual pickup is unaffected. (Not logged again"
                " this session.)"
            )
        return False
    try:
        allowed = game.PickupQuery(caller.Pawn, pickup)
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] PickupQuery failed: {ex!r}")
        return False
    if not allowed:
        logging.warning(
            f"[AutoLootBL1E] PickupQuery refused {comparison_group(pickup.Inventory)}"
            " (the game itself denied it, not our own logic)"
        )
        return False

    count_before = len(inventory_manager.Backpack)
    picking_up = True
    try:
        pickup.GiveTo(caller.Pawn, False)
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] GiveTo failed: {ex!r}")
        return False
    finally:
        picking_up = False
    grew = len(inventory_manager.Backpack) > count_before
    if not grew:
        logging.warning(
            f"[AutoLootBL1E] GiveTo returned but Backpack size stayed at"
            f" {count_before} - pickup did not actually happen"
        )
    return grew


# Network-transition safety guard. Joining a session (or any level travel)
# tears down and rebuilds the Pawn/Controller/InventoryManager, and there is
# no confirmed-safe way to know from here whether that rebuild is complete -
# firing a mutating native call or server RPC (drop, equip, pickup, SDU/
# artifact use) against a half-initialized object during that window is
# exactly the kind of thing that could corrupt more save state than the
# field it directly touches. Confirmed in play: a character's backpack
# capacity, weapon slots and XP were all found reset immediately after
# joining another player's session - cause not confirmed, but the mod issues
# exactly this class of call every tick and had no guard against this at all.
#
# Detected via WorldInfo identity - a new WorldInfo instance means a new
# level/session - rather than trying to catch the transition event itself:
# identity comparison is level-triggered and can't be missed regardless of
# what tick PlayerTick happens to resume on, unlike edge-detecting "did a
# join just happen".
last_world_info = None
world_settled_at = None
TRANSITION_GRACE_SECONDS = 10.0


def world_has_settled(obj) -> bool:
    global last_world_info, world_settled_at
    world_info = obj.WorldInfo
    if world_info is not last_world_info:
        last_world_info = world_info
        world_settled_at = None
    try:
        now = world_info.TimeSeconds
    except Exception:  # noqa: BLE001
        return False
    if world_settled_at is None:
        world_settled_at = now + TRANSITION_GRACE_SECONDS
        logging.info(
            f"[AutoLootBL1E] new world/session detected - pausing all"
            f" pickups/drops/equips for {TRANSITION_GRACE_SECONDS:.0f}s while it settles"
        )
    return now >= world_settled_at


@hook("WillowGame.WillowPlayerController:PlayerTick", Type.POST)
def player_tick(obj, _args, _ret, _func):
    global ticks_until_scan, active_last_pass, next_near_loot_report

    ticks_until_scan -= 1
    if ticks_until_scan > 0:
        return

    if obj.Pawn is None:
        ticks_until_scan = SCAN_INTERVAL
        return

    if not world_has_settled(obj):
        ticks_until_scan = SCAN_INTERVAL
        return

    try:
        # Fill empty slots first, so a gun that lands in one is available to
        # the dry-weapon logic below on this same pass.
        fill_empty_equip_slots(obj)
        refill_dry_backup_slots(obj)
        diversify_equipped_elements(obj)
        manage_weapon_ammo(obj)
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not manage equipment: {ex!r}")

    update_seen_ids(obj)

    try:
        max_dist = (
            obj.GetWillowGlobals().GetGlobalsDefinition().PlayerInteractionDistance
            * range_percent.value
            / 100
        )
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not read pickup range: {ex!r}")
        ticks_until_scan = SCAN_INTERVAL
        return

    view_location = obj.CalcViewActorLocation
    cap = character_level(obj)

    candidates = nearby_pickups(view_location, max_dist)

    # Default in case the try below fails before assigning it - now is also
    # used later, for log throttling, well outside this try/except.
    now = 0.0
    try:
        now = obj.WorldInfo.TimeSeconds
        # nearby_pickups() is every WillowPickup in range, including ammo/
        # health/currency drops we don't track at all - only a candidate this
        # mod actually cares about (should_pickup) should trigger the "near
        # loot" summary, not just standing near an ammo pile.
        near_tracked_loot = any(
            should_pickup(pickup.Inventory, obj)
            for pickup in candidates
            if pickup.Inventory is not None
        )
        if now >= next_near_loot_report and near_tracked_loot:
            report_backpack(obj)
            next_near_loot_report = now + hud_summary_seconds.value
    except Exception as ex:  # noqa: BLE001
        logging.warning(f"[AutoLootBL1E] could not check for nearby loot: {ex!r}")

    collected_any = False
    freed_any_slot = False
    have_cached_real_items = False
    cached_real_items = []

    for pickup in candidates:
        try:
            inventory = pickup.Inventory
            if inventory is None or inventory.Class is None:
                continue

            # Full trace for anything that isn't a weapon - weapon pickup is
            # already confirmed working, so this is scoped to the categories
            # actually in question (shields/grenade mods/class mods/
            # artifacts/SDUs) rather than spamming on every ammo/health pile
            # in range too. Every gate below logs its own outcome so a
            # non-pickup is never silently unexplained.
            class_name = str(inventory.Class.Name)
            trace_this = class_name in ("WillowEquipAbleItem", "WillowUsableItem")
            if trace_this:
                kind = item_kind(inventory)
                sig_seen = signature_already_seen(inventory)
                passes = should_pickup(inventory, obj)
                log_throttled(
                    now,
                    f"[AutoLootBL1E] trace: class={class_name} kind={kind}"
                    f" signature_already_seen={sig_seen}"
                    f" should_pickup={passes} was_full={backpack_is_full(obj)}",
                )

            if signature_already_seen(inventory):
                continue
            if not should_pickup(inventory, obj):
                continue

            # Simple rule: take anything that passes should_pickup, unless it
            # would overflow the backpack - no pre-check comparing the new
            # item against what is already held UNLESS this specific pickup
            # would take the very last free slot. That earlier, unconditional
            # version of this check (run on every pickup regardless of space)
            # trivially rejected everything on a near-empty backpack, since
            # comparing one incoming item against nothing makes it both the
            # best and the worst of a 1-item pool. Scoping it to "would this
            # leave zero slots free" keeps the actual goal - never let an item
            # take the last slot only to immediately become the next thing
            # thrown back out - without that failure mode, since by the time
            # only one slot is left there is always something real to compare
            # against.
            was_full = backpack_is_full(obj)
            if was_full and drop_lowest_when_full.value:
                if not have_cached_real_items:
                    cached_real_items = droppable_backpack_items(obj)
                    have_cached_real_items = True
                worst = choose_worst_item(cached_real_items, cap, obj, log=True, now=now)
                if worst is None:
                    logging.warning(
                        "[AutoLootBL1E] backpack is full and nothing in it can"
                        " be dropped (all undroppable)"
                    )
                elif throw_backpack_item(obj, worst):
                    freed_any_slot = True
                    have_cached_real_items = False
                    # Defer the actual pickup to the next (fast) rescan rather
                    # than attempting it this same tick - the engine's own
                    # capacity count has been confirmed to still read "full"
                    # for one tick right after a drop that already shrank
                    # Backpack, so a same-tick attempt would just fail again.
                    continue
            elif (
                not was_full
                and drop_lowest_when_full.value
                and backpack_would_take_last_slot(obj)
            ):
                if not have_cached_real_items:
                    cached_real_items = droppable_backpack_items(obj)
                    have_cached_real_items = True
                if cached_real_items:
                    would_be_worst = choose_worst_item(
                        cached_real_items + [inventory], cap, obj, log=True, now=now
                    )
                    # Identity, not a UniqueId-style field comparison - BL1E
                    # items have no such field at all (see
                    # item_composition_signature), and an earlier version of
                    # this check compared a getattr(...)-derived value that
                    # was None on both sides for every weapon, so None == None
                    # was matching regardless of what choose_worst_item
                    # actually picked. Confirmed in play: this unconditionally
                    # rejected the incoming weapon every time, then cascaded
                    # into a real drop (from the was_full branch on a later
                    # candidate in the
                    # same pile) every single tick - a full drop/reject
                    # thrash loop, not just a wrong skip.
                    if would_be_worst is inventory:
                        log_throttled(
                            now,
                            f"[AutoLootBL1E] not taking the last backpack slot for"
                            f" {comparison_group(inventory)} - it would immediately"
                            " become the next item to drop",
                        )
                        continue

            if attempt_pickup(obj, pickup):
                collected_any = True
            elif was_full:
                logging.warning(
                    f"[AutoLootBL1E] wanted {item_kind(inventory)} but backpack"
                    " was full and nothing could be freed for it"
                )
        except Exception as ex:  # noqa: BLE001
            logging.warning(f"[AutoLootBL1E] skipped a pickup: {ex!r}")

    use_backpack_extras(obj)
    maybe_use_healing_kit(obj)

    active_this_pass = collected_any or freed_any_slot
    ticks_until_scan = FAST_SCAN_INTERVAL if active_this_pass else SCAN_INTERVAL

    # Report once the pile/cleanup is finished, not per item - same reasoning
    # for both halves: show_hud_message drops messages shown too close
    # together, so one line per pickup or drop would be unreadable anyway,
    # and an active pass rescans on the very next tick, so the first quiet
    # pass lands almost immediately after the last active one. Used to only
    # watch collected_any, so a pass that only DROPPED something (freed_any_slot,
    # no pickup) never refreshed the summary at all - confirmed in play:
    # dropping an item to make room showed no updated summary until the next
    # unrelated pickup happened to trigger one.
    if active_this_pass:
        active_last_pass = True
    elif active_last_pass:
        active_last_pass = False
        report_backpack(obj)


@hook("WillowGame.WillowPlayerController:StartFire", Type.POST)
def on_start_fire(_obj, args, _ret, _func):
    global fire_held
    if int(getattr(args, "FireModeNum", 0)) == 0:
        fire_held = True


@hook("WillowGame.WillowPlayerController:StopFire", Type.POST)
def on_stop_fire(_obj, args, _ret, _func):
    global fire_held
    if int(getattr(args, "FireModeNum", 0)) == 0:
        fire_held = False


@hook("WillowGame.WillowPickup:FailedPickup", Type.PRE)
def block_failed_pickup(_obj, _args, _ret, _func):
    # Suppress only for our own attempts (picking_up), same as AutoLoot -
    # picking something up by hand should still report normally.
    return Block if picking_up else None


MOD_OPTIONS = [
    pickup_weapons,
    pickup_shields,
    pickup_grenade_mods,
    pickup_class_mods,
    pickup_artifacts,
    pickup_sdus,
    auto_use_artifacts,
    auto_use_sdus,
    auto_use_healing_kit_at_health_percent,
    drop_lowest_when_full,
    auto_equip,
    switch_when_empty,
    range_percent,
    hud_summary_seconds,
    summary_in_console,
]

build_mod(options=MOD_OPTIONS)
