import uuid
from dataclasses import dataclass, field, InitVar
from typing import List, Dict, Optional, Any, Tuple, Callable, AnyStr, Set
from pm4py.objects.process_tree.obj import Operator as OP
import pm4py
from pm4py.objects.ocel.obj import OCEL
from pm4py.objects.process_tree.obj import ProcessTree
from enum import Enum
from graphviz import Digraph
import json
import pickle
from pm4py.objects.ocel import constants
from pm4py.util import exec_utils
from pm4py.util.constants import DEFAULT_BGCOLOR
from pm4py.objects.ocel.exporter.jsonocel.variants.classic import Parameters
from datetime import date, datetime
from pm4py.visualization.ocel.ocpn.variants.wo_decoration import ot_to_color
from pm4py.objects.petri_net.obj import PetriNet
import tempfile
from pm4py.visualization.ocel.ocpn import visualizer as ocpn_visualizer

from pd_wpt import apply as ocpd


def json_serial(obj):
    """JSON serializer for objects not serializable by default json code"""

    if isinstance(obj, (datetime, date)):
        return obj.isoformat()
    raise TypeError("Type %s not serializable" % type(obj))

MODEL_SIZE = 60

MAPPING = "mapping"

NEW = "new"

OLD = "old"

# Record Object Type Prefix, i.e., without Workflow
NAMESPACE_RECORD = "record"
NAMESPACE_DEVICES = "workflow:devices"
NAMESPACE_RESOURCES = "workflow:resources"
# Workflow Object Type Prefix
NAMESPACE_WORKFLOW = "workflow"
NAMESPACE_SUBPROCESS = "workflow:sub"
NAMESPACE_LIFECYCLE = "workflow:lc"
# Abstraction Object Type Prefix
NAMESPACE_ABSTRACTION = "abstraction"

HISTORY_OT = NAMESPACE_ABSTRACTION + ":history"
HISTORY_CURRENT = "current"

OCEL_GLOBAL = constants.OCEL_GLOBAL_LOG
OCEL_VERSION = constants.OCEL_GLOBAL_LOG_VERSION
OCEL_ORDERING = constants.OCEL_GLOBAL_LOG_ORDERING
OCEL_ATTN = constants.OCEL_GLOBAL_LOG_ATTRIBUTE_NAMES
OCEL_OBJT = constants.OCEL_GLOBAL_LOG_OBJECT_TYPES
OCEL_GE = constants.OCEL_GLOBAL_EVENT
OCEL_GO = constants.OCEL_GLOBAL_OBJECT
OCEL_ACT = constants.DEFAULT_EVENT_ACTIVITY
OCEL_TYPE = constants.DEFAULT_OBJECT_TYPE
OCEL_EVENTS = constants.OCEL_EVENTS_KEY
OCEL_OBJECTS = constants.OCEL_OBJECTS_KEY
OCEL_TIME = constants.DEFAULT_EVENT_TIMESTAMP
OCEL_OMAP = constants.OCEL_OMAP_KEY
OCEL_VMAP = constants.OCEL_VMAP_KEY
OCEL_OVMAP = constants.OCEL_OVMAP_KEY
OCEL_NA = "__INVALID__"
EXTERNAL = "external"

SUB_ROOT = "sub:root"
LC_DELIMITER = "§"
ABS_DELIMITER = "$"

PT = "process_trees"
PN = "petri_nets"

OT = "object_type"
AGG = "agg"
TR = "trans"
ENTRY_PLACE = "entry"
EXIT_PLACE = "exit"

FUSED_IN = "fused_in_places"
FUSED_OUT = "fused_out_places"


class AvailableAggregations(Enum):
    CAA = 'caa'
    CLA = 'cla'
    IMSEQ = 'seq'
    IMXOR = 'xor'
    IMAND = 'and'
    IMLOOP = 'loop'


PT_OP_TO_AGG = {
    OP.SEQUENCE: AvailableAggregations.IMSEQ,
    OP.XOR: AvailableAggregations.IMXOR,
    OP.PARALLEL: AvailableAggregations.IMAND,
    OP.LOOP: AvailableAggregations.IMLOOP
}

PT_OP_TO_STR = {
    AvailableAggregations.IMSEQ.value: "->",
    AvailableAggregations.IMXOR.value: "X",
    AvailableAggregations.IMAND.value: "+",
    AvailableAggregations.IMLOOP.value: "*"
}


def get_id() -> AnyStr:
    return str(uuid.uuid4())


def initialize_history(aoi: AnyStr) -> tuple[AnyStr, dict[Any, Any]]:
    hid = get_id()
    return hid, {
        OCEL_TYPE: HISTORY_OT,
        OCEL_OVMAP: {
            HISTORY_CURRENT: [aoi]
        }
    }


def transition_log(log: Dict,
                   aoi: AnyStr,
                   aot: AnyStr,
                   events: List[AnyStr],
                   apply_mode: Any = True,
                   parameters: Optional[Dict[Any, Any]] = None) -> Tuple[Dict, AnyStr]:
    events_set = set(events)
    for eid, event in log[constants.OCEL_EVENTS_KEY].items():
        if apply_mode:
            if eid in events_set:
                event[constants.OCEL_OMAP_KEY] = event[constants.OCEL_OMAP_KEY] + [aoi]
        else:
            event[constants.OCEL_OMAP_KEY] = [oid for oid in event[constants.OCEL_OMAP_KEY] if oid != aoi]
    history_present = False
    dummy = True
    remove_oid = None
    for oid, obj in log[constants.OCEL_OBJECTS_KEY].items():
        if not apply_mode and obj[constants.DEFAULT_OBJECT_TYPE] == aot:
            # Need to remove the redone abstraction object
            remove_oid = oid
        if not history_present:
            history_present = obj[constants.DEFAULT_OBJECT_TYPE] == HISTORY_OT
        if history_present and dummy:
            hid = oid
            dummy = False
    if apply_mode:
        # Need to add a new abstraction object
        log[constants.OCEL_OBJECTS_KEY][aoi] = {
            constants.DEFAULT_OBJECT_TYPE: aot,
            constants.OCEL_OVMAP_KEY: {}}
    if apply_mode:
        if history_present:
            # Only add to ovmap of history object
            log[constants.OCEL_OBJECTS_KEY][hid][OCEL_OVMAP][HISTORY_CURRENT].append(aoi)
        else:
            # Set history object
            hid, history = initialize_history(aoi)
            log[constants.OCEL_OBJECTS_KEY][hid] = history
        log[constants.OCEL_GLOBAL_LOG][constants.OCEL_GLOBAL_LOG_OBJECT_TYPES] += [HISTORY_OT, aot]
        log[constants.OCEL_GLOBAL_LOG][constants.OCEL_GLOBAL_LOG_ATTRIBUTE_NAMES] += [
            HISTORY_CURRENT]
    else:
        # Can only redo, if something was there before -> history has to be initialized already
        log[constants.OCEL_OBJECTS_KEY][hid][OCEL_OVMAP][HISTORY_CURRENT].remove(aoi)
        del log[constants.OCEL_OBJECTS_KEY][remove_oid]
    return log, hid


# Event Log State Transition for CAA
# By means of et, we can always determine the events to be aggregated given
# the to be aggregated transitions from the currently available to be applied
# aggregations
def agg_caa(log: Dict,
            events: List[AnyStr],
            ot: AnyStr,
            apply_mode: Any = True,
            aoi: AnyStr = "",
            aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_simple_agg_string(ot, AvailableAggregations.CAA)
    return transition_log(log, aoi, aot, events, apply_mode)


def get_simple_agg_string(ot, agg):
    return f"{NAMESPACE_ABSTRACTION}:{ot}{ABS_DELIMITER}{agg.value}"


def get_complex_agg_string(ot, agg, events):
    return f"{NAMESPACE_ABSTRACTION}:{ot}{ABS_DELIMITER}{agg.value}{ABS_DELIMITER}{hash_eids(events)}"


def agg_cla(log: Dict,
            events: List[AnyStr],
            ot: AnyStr,
            apply_mode: Any = True,
            aoi: AnyStr = "",
            aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_simple_agg_string(ot, AvailableAggregations.CLA)
    return transition_log(log, aoi, aot, events, apply_mode)


def agg_imseq(log: Dict,
              events: List[AnyStr],
              ot: AnyStr,
              apply_mode: Any = True,
              aoi: AnyStr = "",
              aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_complex_agg_string(ot, AvailableAggregations.IMSEQ, events)
    return transition_log(log, aoi, aot, events, apply_mode)
    # transitioned_log_dict = transition_log(log, aoi, aot, events, apply_mode)
    # return construct_ocel(transitioned_log_dict)


def agg_imxor(log: Dict,
              events: List[AnyStr],
              ot: AnyStr,
              apply_mode: Any = True,
              aoi: AnyStr = "",
              aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_complex_agg_string(ot, AvailableAggregations.IMXOR, events)
    return transition_log(log, aoi, aot, events, apply_mode)


def agg_imand(log: Dict,
              events: List[AnyStr],
              ot: AnyStr,
              apply_mode: Any = True,
              aoi: AnyStr = "",
              aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_complex_agg_string(ot, AvailableAggregations.IMAND, events)
    return transition_log(log, aoi, aot, events, apply_mode)


def agg_imloop(log: Dict,
               events: List[AnyStr],
               ot: AnyStr,
               apply_mode: Any = True,
               aoi: AnyStr = "",
               aot: AnyStr = "") -> Tuple[Dict, AnyStr]:
    if apply_mode:
        aoi = get_id()
        aot = get_complex_agg_string(ot, AvailableAggregations.IMLOOP, events)
    return transition_log(log, aoi, aot, events, apply_mode)


def get_activites_for_operator(pt):
    activities = set()
    if pt.label is not None:
        activities.add(pt.label)
    queue = [pt.children]
    while queue:
        active = queue.pop(0)
        for child in active:
            if child.label is not None:
                activities.add(child.label)
            queue.append(child.children)
    return activities


@dataclass
class AggregationRepository:
    repo: Dict[AvailableAggregations, Callable] = field(default_factory=lambda: {AvailableAggregations.CAA: agg_caa,
                                                                                 AvailableAggregations.CLA: agg_cla,
                                                                                 AvailableAggregations.IMSEQ: agg_imseq,
                                                                                 AvailableAggregations.IMXOR: agg_imxor,
                                                                                 AvailableAggregations.IMAND: agg_imand,
                                                                                 AvailableAggregations.IMLOOP: agg_imloop})


def infer_sub_hierarchy(ocel, ocpn):
    pm4py.write_ocel_json(ocel, f"temp.jsonocel")
    with open(f"temp.jsonocel") as f:
        ocel_json_hierarchy = json.loads(f.read())
        f.close()
    sub_interactions = set()
    # First subprocess is always the topmost
    top_time = datetime.max
    top_event = None
    top_subprocesses = None
    labels_to_subprocesses = {}
    labels_to_ots = {}
    for i, e in ocel_json_hierarchy[OCEL_EVENTS].items():
        lc_ot = None
        current_ots = [ocel_json_hierarchy[OCEL_OBJECTS][ot][OCEL_TYPE] for ot in e[OCEL_OMAP]]
        # All ots of an activity label to determine the maximum interaction transition labelled with act
        if e[OCEL_ACT] in labels_to_ots:
            diff = set(current_ots).difference(labels_to_ots[e[OCEL_ACT]])
            if len(diff) > 0:
                labels_to_ots[e[OCEL_ACT]].union(diff)
        else:
            labels_to_ots[e[OCEL_ACT]] = set(current_ots)
        # All timestamps in same timezone
        try:
            current_ts = datetime.strptime(e[OCEL_TIME].split("+")[0], "%Y-%m-%dT%H:%M:%S.%f")
        except ValueError:
            current_ts = datetime.strptime(e[OCEL_TIME].split("+")[0], "%Y-%m-%dT%H:%M:%S")
        first_sub = []
        for ot in current_ots:
            if NAMESPACE_SUBPROCESS in ot:
                first_sub.append(ot)
            elif NAMESPACE_LIFECYCLE in ot:
                lc_ot = ot
        if current_ts < top_time and len(first_sub) > 0:
            top_time = current_ts
            top_subprocesses = first_sub
            top_event = e
        if len(first_sub) == 2:
            to_add = tuple(first_sub)
            if to_add not in sub_interactions and (to_add[1], to_add[0]) not in sub_interactions:
                sub_interactions.add(to_add)
            # if e[OCEL_ACT] not in labels_to_subprocesses:
            invoked_sub = [s for s in first_sub if e[OCEL_VMAP][SUB_ROOT] not in s][0]
            labels_to_subprocesses[e[OCEL_ACT]] = {NAMESPACE_LIFECYCLE: lc_ot,
                                                   NAMESPACE_SUBPROCESS: invoked_sub}
            # else:
            #    invoked_sub = [s for s in first_sub if e[OCEL_VMAP][SUB_ROOT] not in s][0]
            #    labels_to_subprocesses[e[OCEL_ACT]] = {NAMESPACE_LIFECYCLE: lc_ot,
            #                                          NAMESPACE_SUBPROCESS: invoked_sub}
        elif len(first_sub) > 2:
            print("This should not happen.")
        elif len(first_sub) == 1:
            # Only single subprocess, i.e., no hierarchy necessary
            if e[OCEL_ACT] not in labels_to_subprocesses and lc_ot is not None:
                labels_to_subprocesses[e[OCEL_ACT]] = {NAMESPACE_LIFECYCLE: lc_ot,
                                                       NAMESPACE_SUBPROCESS: first_sub[0]}
            elif e[OCEL_ACT] not in labels_to_subprocesses and lc_ot is None:
                labels_to_subprocesses[e[OCEL_ACT]] = {NAMESPACE_SUBPROCESS: first_sub[0]}
            else:
                # This gets difficult, since it means that depending on DATA the respective subprocess is decided -> currently we do not support his
                pass
        else:
            # No supbrocesses existing
            if e[OCEL_ACT] not in labels_to_subprocesses and lc_ot is not None:
                labels_to_subprocesses[e[OCEL_ACT]] = {NAMESPACE_LIFECYCLE: lc_ot}
            elif e[OCEL_ACT] not in labels_to_subprocesses and lc_ot is None:
                labels_to_subprocesses[e[OCEL_ACT]] = {}
            else:
                # This gets difficult, since it means that depending on DATA the respective subprocess is decided -> currently we do not support his
                pass

        #

    petri_nets = ocpn["petri_nets"]
    if top_subprocesses is None:
        # has no subprocess set
        top_name = ""
    elif len(top_subprocesses) == 2:
        # If the topmost subprocess starts with a subprocess, then we need the sub:root attribute to decide which is top
        top_name = f"{NAMESPACE_SUBPROCESS}:{top_event[OCEL_VMAP][SUB_ROOT]}"
        # Topmost activity needs to link to subprocess instead of lifecycle
        petri_net = petri_nets[top_name]
        # top_subprocess = SubprocessNet(petri_net=petri_net,
        #                               petri_nets=petri_nets,
        #                               subprocesses_dict=labels_to_subprocesses,
        #                               visited=set())
    elif len(top_subprocesses) > 0:
        top_name = top_subprocesses[0]
        petri_net = petri_nets[top_name]
        # top_subprocess = SubprocessNet(petri_net=petri_net,
        #                               petri_nets=petri_nets,
        #                               subprocesses_dict=labels_to_subprocesses,
        #                               visited=set())
    else:
        top_name = ""
    return {"interactions": sub_interactions,
            # "subprocesses": top_subprocess,
            "hierarchy": labels_to_subprocesses,
            "top": top_name,
            "ots": labels_to_ots}


@dataclass
class ProcessAggregationTree:
    agg_type: AvailableAggregations
    agg: Callable
    labels: List[AnyStr]
    eids: List[AnyStr]
    mode: InitVar[Any] = False
    pt: InitVar[ProcessTree | None] = None
    adm_im: InitVar[Dict | None] = None
    ar: InitVar[AggregationRepository | None] = None
    te: InitVar[Dict | None] = None
    children: Optional[List[Any]] = field(default_factory=lambda: [])

    def __post_init__(self, mode, pt, adm_im, ar, te):
        if mode:
            queue = [pt.children]
            while queue:
                active = queue.pop(0)
                for child in active:
                    labels = get_activites_for_operator(child)
                    if all([adm_im[act] for act in labels]) and child.operator is not None:
                        self.children.append(
                            ProcessAggregationTree(
                                PT_OP_TO_AGG[child.operator],
                                ar.repo[PT_OP_TO_AGG[child.operator]],
                                labels,
                                [eid for lab in labels for eid in te[lab]],
                                mode=True,
                                pt=child,
                                adm_im=adm_im,
                                te=te,
                                ar=ar
                            )
                        )
                    else:
                        queue.append(child.children)


def check_interleaving_lc(ocpn, ots):
    transition_systems = {}
    all_interactions = {}
    other_ots = [ot for ot in ots if not ot.startswith(NAMESPACE_LIFECYCLE)]
    activities = [act.split(":")[2] for act in [ot for ot in ots if ot.startswith(NAMESPACE_LIFECYCLE)]]
    all_activities = [act for act in ocpn["activities"] if not LC_DELIMITER in act] + activities
    to_add = set()
    for ot in other_ots:
        transition_systems[ot] = pm4py.objects.petri_net.utils.reachability_graph.construct_reachability_graph(
            ocpn[PN][ot][0], ocpn[PN][ot][1])
        queue = [s for s in transition_systems[ot].states if s.name == "source1"]
        # queue = [t for t in transition_systems[top].transitions if t.from_state == start]
        visited = [queue[0]]
        visited_tr = []
        # visited.add(queue[0])
        # open = {tr.name.split(",")[1] for tr in ts}
        names = []
        nones = []
        while queue:
            active = queue.pop(0)
            for tr in active.outgoing:
                if tr.to_state not in visited:
                    # Check for reachability "meeting" at the same place again
                    visited.append(tr.to_state)
                    queue.append(tr.to_state)
            for tr in active.incoming:
                if "None" not in tr.name:
                    try:
                        name = tr.name.split("'")[1]
                    except IndexError:
                        nones.append(name)
                        break
                    names.append(name)

        all_interactions[ot] = {k: dict(c=0, e=list()) for k in all_activities}
        # Lifecycle interactions
        for i in range(len(names) - 1):
            name1 = names[i].split(LC_DELIMITER)[0]
            name2 = names[i + 1].split(LC_DELIMITER)[0]
            try:
                if name1 != name2:
                    if all_interactions[ot][name2]["c"] > 0:
                        all_interactions[ot][name1]["e"].append(name2)
                        all_interactions[ot][name2]["e"].append(name1)
                        to_add.add(name2)
                    else:
                        all_interactions[ot][name1]["c"] += 1
                else:
                    all_interactions[ot][name1]["c"] += 1
            except KeyError:
                to_add.add(name2)
    return to_add


def compute_at(log: OCEL,
               ocpn: Any,
               ar: AggregationRepository,
               te: Dict[AnyStr, Set[AnyStr]]) -> Tuple[Dict[AnyStr, ProcessAggregationTree], Any]:
    ots = list(ocpn[PN].keys())
    at = {ot: {} for ot in ots}
    # Has lifecycles
    has_lc = len([ot for ot in ots if ot.startswith(NAMESPACE_LIFECYCLE)]) > 0
    # Subprocess hierarchy needs to be determined
    hierarchy = infer_sub_hierarchy(log, ocpn)
    labels_to_ots = hierarchy["ots"]
    if has_lc:
        # self, lc, one interaction
        act_labels_to_ots = {}
        for lab in labels_to_ots:
            act = lab.split(LC_DELIMITER)[0]
            if act in act_labels_to_ots:
                act_labels_to_ots[act] = act_labels_to_ots[act].union(labels_to_ots[lab])
            else:
                act_labels_to_ots[act] = labels_to_ots[lab]
        interleavings = check_interleaving_lc(ocpn, ots)
        adm_lc = {act: len(d) <= 3 and act not in interleavings for act, d in act_labels_to_ots.items()}
        # self, lc
        adm_im = {act: len([ot for ot in d if not ot.startswith(NAMESPACE_LIFECYCLE)]) < 2 for act, d in
                  labels_to_ots.items()}
    else:
        # self
        adm_im = {act: len(d) <= 1 for act, d in labels_to_ots.items()}
    for ot in ots:
        if ot.startswith(NAMESPACE_LIFECYCLE):
            # CLA
            act = ot.split(":")[2]
            try:
                if adm_lc[act]:
                    labels = [lab for lab in labels_to_ots if lab.startswith(act)]
                    at[ot] = ProcessAggregationTree(
                        AvailableAggregations.CLA,
                        ar.repo[AvailableAggregations.CLA],
                        labels,
                        [eid for lab in labels for eid in te[lab]])
            except KeyError:
                pass
        # elif (ot.startswith(NAMESPACE_SUBPROCESS) or ot.startswith(NAMESPACE_DEVICES) or ot.startswith(
        #        NAMESPACE_RESOURCES)) \
        #        and ot != hierarchy["top"]:
        #    # CAA for Subprocess, Devices, Resources -> always admissible
        #    labels = [tr.label for tr in ocpn[PN][ot][0].transitions if tr.label is not None]
        #    at[ot] = ProcessAggregationTree(
        #        AvailableAggregations.CAA,
        #        ar.repo[AvailableAggregations.CAA],
        #        labels,
        #        [eid for lab in labels for eid in te[lab]])
        else:
            # IM / CAA for Business Object or topmost subprocess
            pt = ocpn[PT][ot]
            if pt.label is not None and adm_im[pt.label]:
                # Only a single leaf as process tree
                at[ot] = ProcessAggregationTree(
                    AvailableAggregations.CAA,
                    ar.repo[AvailableAggregations.CAA],
                    [pt.label],
                    [eid for lab in labels for eid in te[lab]]
                )
            else:
                labels = [tr.label for tr in ocpn[PN][ot][0].transitions if tr.label is not None]
                if all([adm_im[act] for act in labels]):
                    at[ot] = ProcessAggregationTree(
                        AvailableAggregations.CAA,
                        ar.repo[AvailableAggregations.CAA],
                        labels,
                        [eid for lab in labels for eid in te[lab]],
                        children=[ProcessAggregationTree(
                            PT_OP_TO_AGG[pt.operator],
                            ar.repo[PT_OP_TO_AGG[pt.operator]],
                            labels,
                            [eid for lab in labels for eid in te[lab]],
                            mode=True,
                            pt=pt,
                            adm_im=adm_im,
                            te=te,
                            ar=ar
                        )])
                else:
                    at[ot] = ProcessAggregationTree(
                        AvailableAggregations.CAA,
                        ar.repo[AvailableAggregations.CAA],
                        labels,
                        [eid for lab in labels for eid in te[lab]],
                        mode=True,
                        pt=pt,
                        adm_im=adm_im,
                        te=te,
                        ar=ar
                    )
    return at, hierarchy

    # Have to check for applicability, i.e., the tree should only contain aggregations that are indeed applicable
    # + have to see how I can do it with redoing lifecycle aggregations for somethin that has not been visible before
    # need to store the event list and hash of event list in time sorted order to quickly determine the correct state in
    # the retrieve functions


def hash_eids(eids: List[AnyStr]) -> int:
    return hash(";".join(eids))


# Aggregation, List of transition labels to be aggregated
# from OTs to Dict from name to CLA, CAA for lower-level Supbprocesses, CAA for Devices, CAA for Resources, Process Tree, CAA
def retrieve_next(log: Dict,
                  at: Any,
                  hid: AnyStr,
                  hierarchy: Any) -> Tuple[AnyStr, AvailableAggregations, List[AnyStr]]:
    at_bos, at_devices, at_lcs, at_resources, sub_list = extract_from_at(at, hierarchy)
    if hid == "":
        # First time
        all_bos_in_order_dict = {}
        for bo in at_bos:
            bo_list = [(bo, at[bo].agg_type.value, hash_eids(at[bo].eids), at[bo].eids)]
            queue = [at[bo]]
            while queue:
                active = queue.pop(0)
                for child in active.children:
                    bo_list.append((bo, child.agg_type.value, hash_eids(child.eids), child.eids))
                    queue.append(child)
            bo_list.reverse()
            all_bos_in_order_dict[bo] = bo_list
        all_bos_in_order = []
        lengths = [len(all_bos_in_order_dict[k]) for k in at_bos]
        min_lengths = min(lengths)
        max_lengths = max(lengths)
        i = 0
        while i < min_lengths:
            # Round rubin working way upwards
            all_bos_in_order += [all_bos_in_order_dict[k][i] for k in at_bos]
            i += 1
        for i in range(min_lengths, max_lengths):
            for j in range(len(at_bos)):
                if i < lengths[j]:
                    all_bos_in_order.append(all_bos_in_order_dict[at_bos[j]][i])
        with open(f"bo_order", 'wb') as outp:
            pickle.dump(all_bos_in_order, outp, pickle.HIGHEST_PROTOCOL)

        return extract_next_agg(at, at_bos, at_devices, at_lcs, at_resources, sub_list)
    else:
        aot_len, aots, dev_list_len, lcs_len, res_list_len, sub_list_len = extract_history_and_lengths(at_devices,
                                                                                                       at_lcs,
                                                                                                       at_resources,
                                                                                                       hid, log,
                                                                                                       sub_list)
        if aot_len < lcs_len:
            at_lcs = [aot for aot in at_lcs if get_simple_agg_string(aot, AvailableAggregations.CLA) not in aots]
            return extract_next_agg(at, at_bos, at_devices, at_lcs, at_resources, sub_list)
        elif lcs_len <= aot_len < sub_list_len:
            sub_list = [aot for aot in sub_list if get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return extract_next_agg(at, at_bos, at_devices, [], at_resources, sub_list)
        elif sub_list_len <= aot_len < dev_list_len:
            at_devices = [aot for aot in at_devices if
                          get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return extract_next_agg(at, at_bos, at_devices, [], at_resources, [])
        elif dev_list_len <= aot_len < res_list_len:
            at_resources = [aot for aot in at_resources if
                            get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return extract_next_agg(at, at_bos, [], [], at_resources, [])
        else:
            # Goes into bo trees -> have to use hashes to uniquely determine the agg
            aots = aots[res_list_len:]
            with open(f"bo_order", 'rb') as outp:
                all_bos_in_order = pickle.load(outp)
                outp.close()
            if aot_len > res_list_len + len(all_bos_in_order):
                # This cannot happen, more aggregations in history than can be applied
                raise RuntimeError(
                    "Too many aggregations are stored in the history than are applicable according to the aggregation tree.")

            aots_tuple = [(aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                           aot.split(ABS_DELIMITER)[1],
                           aot.split(ABS_DELIMITER)[2]) if len(aot.split(ABS_DELIMITER)) > 2
                          else (aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                                aot.split(ABS_DELIMITER)[1]) for aot in aots]
            aots_left = []
            with_caa = False
            for i in range(len(all_bos_in_order)):
                if all_bos_in_order[i][1] == AvailableAggregations.CAA.value:
                    # CAA
                    if not (all_bos_in_order[i][0], all_bos_in_order[i][1]) in aots_tuple:
                        aots_left.append(all_bos_in_order[i])
                else:
                    if not (all_bos_in_order[i][0], all_bos_in_order[i][1], str(all_bos_in_order[i][2])) in aots_tuple:
                        aots_left.append(all_bos_in_order[i])

            #    aot_left = aots_left[aot_len - res_list_len]

            aot_left = aots_left[0]
            return aot_left[0], AvailableAggregations(aot_left[1]), aot_left[3]


def extract_history_and_lengths(at_devices, at_lcs, at_resources, hid, log, sub_list):
    history = log[constants.OCEL_OBJECTS_KEY][hid]
    applied = history[constants.OCEL_OVMAP_KEY][HISTORY_CURRENT]
    aots = [log[constants.OCEL_OBJECTS_KEY][aoi][constants.DEFAULT_OBJECT_TYPE] for aoi in applied]
    # Cumulative lengths
    aot_len = len(aots)
    lcs_len = len(at_lcs)
    sub_list_len = lcs_len + len(sub_list)
    dev_list_len = sub_list_len + len(at_devices)
    res_list_len = dev_list_len + len(at_resources)
    return aot_len, aots, dev_list_len, lcs_len, res_list_len, sub_list_len


def extract_from_at(at, hierarchy):
    # First CLA
    at_lcs = [aot for aot in at if aot.startswith(NAMESPACE_LIFECYCLE) and type(at[aot]) is ProcessAggregationTree]
    # Then CAA for lower-level Subprocesses
    sub_list = [hierarchy["top"]]
    queue = [hierarchy["top"]]
    while queue:
        active = queue.pop(0)
        children_tuples = [sub for sub in hierarchy["interactions"] if sub[0] == active or sub[1] == active]
        for child in children_tuples:
            if child[0] == active and child[1] not in sub_list:
                queue.append(child[1])
                sub_list.append(child[1])
            elif child[1] == active and child[0] not in sub_list:
                queue.append(child[0])
                sub_list.append(child[0])
    # Top should not be aggregated at beginning
    sub_list = sub_list[1:]
    sub_list.reverse()
    # CAA for Devices
    at_devices = [aot for aot in at if aot.startswith(NAMESPACE_DEVICES)]
    # CAA for Resources
    at_resources = [aot for aot in at if aot.startswith(NAMESPACE_RESOURCES)]
    # BO CAA + Process Tree
    at_bos = [aot for aot in at if
              aot not in at_lcs and aot not in sub_list and aot not in at_devices and aot not in at_resources
              and type(at[aot]) is ProcessAggregationTree]
    return at_bos, at_devices, at_lcs, at_resources, sub_list


def extract_next_agg(at, at_bos, at_devices, at_lcs, at_resources, sub_list):
    if len(at_lcs) > 0:
        lc = at_lcs[0]
        ot = lc
        agg_tree = at[lc]
    elif len(sub_list) > 0:
        sub = sub_list[0]
        ot = sub
        agg_tree = at[sub]
    elif len(at_devices) > 0:
        dev = at_devices[0]
        ot = dev
        agg_tree = at[dev]
    elif len(at_resources) > 0:
        res = at_resources[0]
        ot = res
        agg_tree = at[res]
    else:
        # Only for initializing
        bo = at_bos[0]
        ot = bo
        bo_list = [at[bo]]
        queue = [at[bo]]
        while queue:
            active = queue.pop(0)
            for child in active.children:
                bo_list.append(child)
                queue.append(child)
        bo_list.reverse()
        agg_tree = bo_list[0]
    return ot, agg_tree.agg_type, agg_tree.eids


# Dict from ot to Aggregation, List of transition labels to be aggregated
def retrieve_available(log: Dict,
                       at: Any,
                       hid: AnyStr,
                       hierarchy: Any) -> Dict[AnyStr, Tuple[AnyStr, AvailableAggregations, List[AnyStr]]]:
    at_bos, at_devices, at_lcs, at_resources, sub_list = extract_from_at(at, hierarchy)
    if hid == "":
        raise RuntimeError("Retrieve available has to be called with a valid history object identifier hid.")
    else:
        aot_len, aots, dev_list_len, lcs_len, res_list_len, sub_list_len = extract_history_and_lengths(at_devices,
                                                                                                       at_lcs,
                                                                                                       at_resources,
                                                                                                       hid, log,
                                                                                                       sub_list)
        if aot_len < lcs_len:
            # First CLAs
            at_lcs = [aot for aot in at_lcs if get_simple_agg_string(aot, AvailableAggregations.CLA) not in aots]
            return {lc: (lc, at[lc].agg_type, at[lc].eids) for lc in at_lcs}
        elif lcs_len <= aot_len < sub_list_len:
            # Then CAAs for subs
            sub_list = [aot for aot in sub_list if get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return {sub: (sub, at[sub].agg_type, at[sub].eids) for sub in sub_list}
        elif sub_list_len <= aot_len < dev_list_len:
            at_devices = [aot for aot in at_devices if
                          get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return {dev: (dev, at[dev].agg_type, at[dev].eids) for dev in at_devices}
        elif dev_list_len <= aot_len < res_list_len:
            at_resources = [aot for aot in at_resources if
                            get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return {res: (res, at[res].agg_type, at[res].eids) for res in at_resources}
        else:
            # Goes into bo trees -> have to use hashes to uniquely determine the agg
            aots = aots[res_list_len:]
            with open(f"bo_order", 'rb') as outp:
                all_bos_in_order = pickle.load(outp)
                outp.close()
            if aot_len > res_list_len + len(all_bos_in_order):
                # This cannot happen, more aggregations in history than can be applied
                raise RuntimeError(
                    "Too many aggregations are stored in the history than are applicable according to the aggregation tree.")

            aots_tuple = [(aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                           aot.split(ABS_DELIMITER)[1],
                           aot.split(ABS_DELIMITER)[2]) if len(aot.split(ABS_DELIMITER)) > 2
                          else (aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                                aot.split(ABS_DELIMITER)[1]) for aot in aots]
            aots_left = []
            for i in range(len(all_bos_in_order)):
                if all_bos_in_order[i][1] == AvailableAggregations.CAA.value:
                    # CAA
                    if not (all_bos_in_order[i][0], all_bos_in_order[i][1]) in aots_tuple:
                        aots_left.append(all_bos_in_order[i])
                else:
                    if not (all_bos_in_order[i][0], all_bos_in_order[i][1], str(all_bos_in_order[i][2])) in aots_tuple:
                        aots_left.append(all_bos_in_order[i])

            #    aot_left = aots_left[aot_len - res_list_len]
            ats_ots = {t[0] for t in aots_left}
            upwards_looking_per_ot = {
                ot: [aot for aot in aots_left if aot[0] == ot][0]
                for ot in ats_ots
            }
            return {ot: (upwards_looking_per_ot[ot][0], AvailableAggregations(upwards_looking_per_ot[ot][1]),
                         upwards_looking_per_ot[ot][3])
                    for ot in upwards_looking_per_ot}


def retrieve_redoable(log: Dict,
                      at: Any,
                      hid: AnyStr,
                      hierarchy: Any) -> Dict[AnyStr, Tuple[AnyStr, AvailableAggregations, List[AnyStr]]]:
    at_bos, at_devices, at_lcs, at_resources, sub_list = extract_from_at(at, hierarchy)
    if hid == "":
        raise RuntimeError("Retrieve available has to be called with a valid history object identifier hid.")
    else:
        aot_len, aots, dev_list_len, lcs_len, res_list_len, sub_list_len = extract_history_and_lengths(at_devices,
                                                                                                       at_lcs,
                                                                                                       at_resources,
                                                                                                       hid, log,
                                                                                                       sub_list)
        if aot_len < lcs_len:
            # First CLAs
            at_lcs_from_aots = [lc.removeprefix(NAMESPACE_ABSTRACTION).split(ABS_DELIMITER)[0] for lc in aots]
            return {lc: (lc, at[lc].agg_type, at[lc].eids) for lc in at_lcs_from_aots}
        elif lcs_len <= aot_len < sub_list_len:
            # Need to determine subs to be redone and lcs for visible subs
            remaining_sub = [aot for aot in sub_list if
                             get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            sub_to_lc = set()
            for act, ots in hierarchy["ots"].items():
                ots = list(ots)
                sub_ots = [ot for ot in ots if ot.startswith(NAMESPACE_SUBPROCESS)]
                lc_ots = [ot for ot in ots if ot.startswith(NAMESPACE_LIFECYCLE)]
                for sub in sub_ots:
                    if sub not in remaining_sub:
                        sub_to_lc.union(set(lc_ots))
                        # if sub in sub_to_lc:
                        # sub_to_lc[sub] += lc_ots

                        # else:
                        # sub_to_lc[sub] = lc_ots
            subs_redo = {sub: (sub, at[sub].agg_type, at[sub].eids) for sub in sub_list}
            lc_redo = {lc: (lc, at[lc].agg_type, at[lc].eids) for lc in sub_to_lc}
            return {**subs_redo, **lc_redo}
        elif sub_list_len <= aot_len < dev_list_len:
            at_devices = [aot for aot in at_devices if
                          get_simple_agg_string(aot, AvailableAggregations.CAA) in aots]
            return {dev: (dev, at[dev].agg_type, at[dev].eids) for dev in at_devices}
        elif dev_list_len <= aot_len < res_list_len:
            at_resources = [aot for aot in at_resources if
                            get_simple_agg_string(aot, AvailableAggregations.CAA) not in aots]
            return {res: (res, at[res].agg_type, at[res].eids) for res in at_resources}
        else:
            # Visible: IM
            # Invisible: CAA
            with open(f"bo_order", 'rb') as outp:
                all_bos_in_order = pickle.load(outp)
                outp.close()
            if aot_len > res_list_len + len(all_bos_in_order):
                # This cannot happen, more aggregations in history than can be applied
                raise RuntimeError(
                    "Too many aggregations are stored in the history than are applicable according to the aggregation tree.")

            aots_tuple = [(aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                           aot.split(ABS_DELIMITER)[1],
                           aot.split(ABS_DELIMITER)[2]) if len(aot.split(ABS_DELIMITER)) > 2
                          else (aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"),
                                aot.split(ABS_DELIMITER)[1]) for aot in aots[res_list_len:]][-1]
            caa_redoable = {}
            im_redoable = {aots_tuple[0]: (aots_tuple[0], AvailableAggregations(aots_tuple[1]),
                                           [bo[3] for bo in all_bos_in_order if
                                            bo[0] == aots_tuple[0] and AvailableAggregations(
                                                bo[1]) is AvailableAggregations(aots_tuple[1])
                                            and str(bo[2]) == aots_tuple[2]][0])}
            #                                            and str(bo[2]) == aot.split(ABS_DELIMITER)[2]][0]))
            for aot in aots:
                agg_type = AvailableAggregations(aot.split(ABS_DELIMITER)[1])
                ot = aot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":")
                if agg_type is AvailableAggregations.CAA:
                    caa_redoable[ot] = (ot, agg_type, at[ot].eids)
                # elif agg_type is AvailableAggregations.IMSEQ or agg_type is AvailableAggregations.IMXOR or \
                #    agg_type is AvailableAggregations.IMAND or agg_type is AvailableAggregations.IMLOOP:
                #    if ot in im_redoable:
                #        im_redoable[ot] += [(ot, agg_type, [bo[3] for bo in all_bos_in_order if bo[0] == ot and AvailableAggregations(bo[1]) is agg_type
                #                                            and str(bo[2]) == aot.split(ABS_DELIMITER)[2]][0])]
                #    else:
                #        im_redoable[ot] = [(ot, agg_type, [bo[3] for bo in all_bos_in_order if bo[0] == ot and AvailableAggregations(bo[1]) is agg_type
                #                                            and str(bo[2]) == aot.split(ABS_DELIMITER)[2]][0])]
            return {**caa_redoable, **im_redoable}


def size_digraph(viz: Digraph) -> int:
    return len([el for el in viz.body if "label" in el]) - 2


# Aggregation Tree: Tree of Tuples[AvailalbeAggregations, Events]
# -> Event Log State for Understandable Model, Original Model, Aggregation Tree, et, te
def initialize(ocel_log: OCEL,
               log: Dict,
               ar: AggregationRepository = AggregationRepository()) -> Tuple[
    Dict, Any, Any, Any, Any, Any, AnyStr, Any, AggregationRepository]:
    ot_wf = [ot for ot in pm4py.ocel_get_object_types(ocel_log) if ot.startswith(NAMESPACE_WORKFLOW)]
    log_wf = pm4py.filter_ocel_object_types(ocel_log, ot_wf)
    ocpn = ocpd(log_wf)

    # Check replay
    te = ocpn['activities_indep']['events']
    et = {e: tr for e, tr in [(k, t) for t, eset in te.items() for k in eset]}

    at, hierarchy = compute_at(ocel_log, ocpn, ar, te)
    hid = ""
    viz = overlay(log, ocpn, ar, et, hid)

    while size_digraph(viz) > MODEL_SIZE:
        ot, agg, events = retrieve_next(log, at, hid, hierarchy)
        log, hid = ar.repo[agg](log, events, ot)
        viz = overlay(log, ocpn, ar, et, hid)
    file_path = "initialized_process_model.svg"
    ocpn_visualizer.save(viz, file_path)
    return log, ocpn, at, et, te, hierarchy, hid, viz, ar

def overlay(log: Dict,
            ocpn: Any,
            ar: AggregationRepository,
            et: Dict[AnyStr, AnyStr],
            hid: AnyStr) -> Digraph:
    # Check whether log has history object
    if hid == "":
        # No history object means in initialization -> original ocpn as graphviz object
        return pm4py.visualization.ocel.ocpn.variants.wo_decoration.apply(ocpn)
    else:
        # extract applied value from history object value current
        applied = log[constants.OCEL_OBJECTS_KEY][hid][constants.OCEL_OVMAP_KEY][HISTORY_CURRENT]
        # for i in applied
        esets = {}
        tsets = {}
        hidden_lc_labels = set()
        visible_lc_labels = {i for k, i in et.items()}
        hidden_ot_labels = set()
        visible_ot_labels = {i for k, i in et.items()}
        visible_ots = {ot for ot in ocpn[PN]}
        hidden_labels_to_ot = {}
        im_ots = [log[constants.OCEL_OBJECTS_KEY][aoi][constants.DEFAULT_OBJECT_TYPE]
                  for aoi in applied if
                  len(log[constants.OCEL_OBJECTS_KEY][aoi][constants.DEFAULT_OBJECT_TYPE].split(ABS_DELIMITER)) == 3]
        hidden_act_labels = {ot.split(ABS_DELIMITER)[0].removeprefix(NAMESPACE_ABSTRACTION + ":"): [] for ot in im_ots}
        for aoi in applied:
            aot = log[constants.OCEL_OBJECTS_KEY][aoi][constants.DEFAULT_OBJECT_TYPE]
            aot_split = aot.split(ABS_DELIMITER)
            ot = aot_split[0].removeprefix(NAMESPACE_ABSTRACTION + ":")
            agg_type_value = aot_split[1]
            agg_type = AvailableAggregations(agg_type_value)
            if agg_type not in ar.repo:
                raise RuntimeError("The event log contains abstractions that are not implemented.")
            eset = {eid for eid, e in log[constants.OCEL_EVENTS_KEY].items() if aoi in e[constants.OCEL_OMAP_KEY]}
            esets[aot] = eset
            tset = {et[eid] for eid in eset}
            tsets[aot] = tset
            if agg_type is AvailableAggregations.CLA:
                hidden_lc_labels = hidden_lc_labels.union(tset)
                visible_ots.remove(ot)
            elif agg_type is AvailableAggregations.CAA:
                hidden_ot_labels = hidden_ot_labels.union(tset)
                hidden_labels_to_ot = {**hidden_labels_to_ot, **{label: ot for label in tset}}
                visible_ots.remove(ot)
            elif agg_type in [AvailableAggregations.IMSEQ, AvailableAggregations.IMAND, AvailableAggregations.IMXOR,
                              AvailableAggregations.IMLOOP]:
                if not tset.issubset(hidden_lc_labels):
                    # IM Aggregations are similar to lifecycle aggregations in the sense that transitions in a single ot's
                    # petri net get aggregated into a single transition
                    hidden_act_labels[ot].append({aot: tset})

        visible_lc_labels = visible_lc_labels.difference(hidden_lc_labels)
        visible_ot_labels = visible_ot_labels.difference(hidden_ot_labels).difference(hidden_lc_labels)
        return get_graphviz_for_aggs(ocpn=ocpn,
                                     hidden_lc_labels=hidden_lc_labels,
                                     visible_lc_labels=visible_lc_labels,
                                     hidden_ot_labels=hidden_ot_labels,
                                     visible_ot_labels=visible_ot_labels,
                                     hidden_act_labels=hidden_act_labels,
                                     hidden_labels_to_ot=hidden_labels_to_ot,
                                     visible_ots=visible_ots)


class Parameters(Enum):
    FORMAT = "format"
    BGCOLOR = "bgcolor"
    RANKDIR = "rankdir"


def generate_single_sese_fragment() -> Dict[AnyStr, AnyStr]:
    return {ENTRY_PLACE: str(uuid.uuid4()),
            EXIT_PLACE: str(uuid.uuid4())}


def get_graphviz_for_aggs(ocpn: Any,
                          hidden_lc_labels: Set,
                          visible_lc_labels: Set,
                          hidden_ot_labels: Set,
                          visible_ot_labels: Set,
                          hidden_act_labels: Dict[AnyStr, List[Dict[AnyStr, Set]]],
                          hidden_labels_to_ot: Dict[AnyStr, AnyStr],
                          visible_ots: Set) -> Digraph:
    parameters = dict(LC_DELIMITER=LC_DELIMITER)
    bgcolor = exec_utils.get_param_value(Parameters.BGCOLOR, parameters, DEFAULT_BGCOLOR)
    rankdir = exec_utils.get_param_value(Parameters.RANKDIR, parameters, "LR")
    image_format = exec_utils.get_param_value(Parameters.FORMAT, parameters, "svg")

    lc_activities_map = {}
    activities_map = {}
    source_places = {}
    target_places = {}
    transition_map = {}
    places = {}
    filename = tempfile.NamedTemporaryFile(suffix='.gv')

    activities = {tr.label for sel in visible_ots if not sel.startswith(NAMESPACE_LIFECYCLE) for tr in
                  ocpn["petri_nets"][sel][0].transitions if
                  tr.label is not None}

    viz = Digraph("ocdfg", filename=filename.name, engine='dot', graph_attr={'bgcolor': bgcolor})
    viz.attr('node', shape='ellipse', fixedsize='false')

    # Determine hierarchy, new act labels for IM Aggregations
    agg_hierarchy = {ot: {i: [] for i in range(len(hidden_act_labels[ot]) - 1)} for ot in hidden_act_labels}
    acts_to_new_im = {}
    acts_ot_to_new_im = {ot: {} for ot in hidden_act_labels}
    acts_ot_to_aot = {ot: {} for ot in hidden_act_labels}
    for ot, aggl in hidden_act_labels.items():
        for i in range(len(aggl)):
            for j in range(i + 1, len(aggl)):
                agg1 = aggl[i]
                agg2 = aggl[j]
                aot1 = list(agg1.keys())[0]
                aot2 = list(agg2.keys())[0]
                is_subset = agg1[aot1].issubset(agg2[aot2])
                if is_subset:
                    # agg_hierarchy[ot][i].append((aot1.split(ABS_DELIMITER)[1], j, aot2.split(ABS_DELIMITER)[1]))
                    agg_hierarchy[ot][i].append(j)
                    inner_process_tree_str = "?" + ",?".join(agg2[aot2]).replace(LC_DELIMITER, "-")
                    if len(agg2[aot2]) < 2:
                        inner_process_tree_str += ", tau"
                    new_activity_label = f'{PT_OP_TO_STR[aot2.split(ABS_DELIMITER)[1]]}({inner_process_tree_str})'
                    if new_activity_label not in acts_ot_to_aot[ot]:
                        acts_ot_to_aot[ot][new_activity_label] = [i, j]
                    else:
                        acts_ot_to_aot[ot][new_activity_label] += [i, j]
                    for act in agg2[aot2]:
                        acts_to_new_im[act] = new_activity_label
                        acts_ot_to_new_im[ot][act] = new_activity_label
                else:
                    inner_process_tree_str1 = "?" + ",?".join(agg1[aot1]).replace(LC_DELIMITER, "-")
                    inner_process_tree_str2 = "?" + ",?".join(agg2[aot2]).replace(LC_DELIMITER, "-")
                    if len(agg1[aot1]) < 2:
                        inner_process_tree_str1 += ", tau"
                    new_activity_label1 = f'{PT_OP_TO_STR[aot1.split(ABS_DELIMITER)[1]]}({inner_process_tree_str1})'
                    if new_activity_label1 not in acts_ot_to_aot[ot]:
                        acts_ot_to_aot[ot][new_activity_label1] = [i]
                    else:
                        acts_ot_to_aot[ot][new_activity_label1] += [i]
                    if len(agg2[aot2]) < 2:
                        inner_process_tree_str2 += ", tau"
                    new_activity_label2 = f'{PT_OP_TO_STR[aot2.split(ABS_DELIMITER)[1]]}({inner_process_tree_str2})'
                    if new_activity_label2 not in acts_ot_to_aot[ot]:
                        acts_ot_to_aot[ot][new_activity_label2] = [j]
                    else:
                        acts_ot_to_aot[ot][new_activity_label2] += [j]
                    for act in agg1[aot1]:
                        acts_to_new_im[act] = new_activity_label1
                        acts_ot_to_new_im[ot][act] = new_activity_label1
                    for act in agg2[aot2]:
                        acts_to_new_im[act] = new_activity_label2
                        acts_ot_to_new_im[ot][act] = new_activity_label2
        # all_acts = {act for i, d in hidden_act_labels.items() for acts in d for act in acts}
        if len(acts_ot_to_aot[ot]) < len(hidden_act_labels[ot]):

            aot1 = list(hidden_act_labels[ot][0].keys())[0]
            inner_process_tree_str = "?" + ",?".join(hidden_act_labels[ot][0][aot1]).replace(LC_DELIMITER, "-")
            new_activity_label = f'{PT_OP_TO_STR[aot1.split(ABS_DELIMITER)[1]]}({inner_process_tree_str})'
            if len(aot1) < 2:
                inner_process_tree_str += ", tau"
            for act in hidden_act_labels[ot][0][aot1]:
                acts_to_new_im[act] = new_activity_label
                acts_ot_to_new_im[ot][act] = new_activity_label
            acts_ot_to_aot[ot][new_activity_label] = [0]

    # Special case of only one process tree node
    new_im_to_acts_count = {ot: len(set(acts_ot_to_new_im[ot].values())) for ot in hidden_act_labels}

    activities_to_abstraction = {}
    # Activities
    for act in activities:
        if act in acts_to_new_im:
            # This activity will be aggregated into a higher-level activity corresponding to its process tree parent
            act_processed = acts_to_new_im[act]
        elif act in hidden_lc_labels and (act not in visible_ot_labels and act not in hidden_ot_labels):
            # Lifecycles hidden without subprocess
            act_processed = act.split(parameters["LC_DELIMITER"])[0]
        elif act in visible_lc_labels and (act not in visible_ot_labels and act not in hidden_ot_labels):
            # Lifecycles visible without subprocess
            act_processed = act.replace(parameters["LC_DELIMITER"], "-")
        elif act in hidden_lc_labels and act in visible_ot_labels:
            # Lifecycles hidden with subprocess visible
            act_processed_temp = act.split(parameters["LC_DELIMITER"])[0]
            ot_hidden = hidden_labels_to_ot[act]
            if ot_hidden.startswith(NAMESPACE_SUBPROCESS):
                act_processed = f"{act_processed_temp} -> sub"
            elif ot_hidden.startswith(NAMESPACE_DEVICES):
                act_processed = f"{act_processed_temp} -> dev"
            elif ot_hidden.startswith(NAMESPACE_RESOURCES):
                act_processed = f"{act_processed_temp} -> res"
            else:
                to_be_removed = NAMESPACE_WORKFLOW + ":"
                act_processed = f"{act_processed_temp} <-> {ot_hidden.removeprefix(to_be_removed)}"
        elif act in visible_lc_labels and act in visible_ot_labels:
            # Lifecycles visible with subprocess visible
            act_processed = act.replace(parameters["LC_DELIMITER"], "-")
        elif act in visible_lc_labels and act in hidden_ot_labels:
            # Lifecycles visible with subprocess invisible
            ot_hidden = hidden_labels_to_ot[act]
            act_processed_temp = act.replace(parameters["LC_DELIMITER"], "-")
            if ot_hidden.startswith(NAMESPACE_SUBPROCESS):
                act_processed = f"{act_processed_temp} -> sub"
            elif ot_hidden.startswith(NAMESPACE_DEVICES):
                act_processed = f"{act_processed_temp} -> dev"
            elif ot_hidden.startswith(NAMESPACE_RESOURCES):
                act_processed = f"{act_processed_temp} -> res"
            else:
                to_be_removed = NAMESPACE_WORKFLOW + ":"
                act_processed = f"{act_processed_temp} <-> {ot_hidden.removeprefix(to_be_removed)}"
        elif act in hidden_lc_labels and act in hidden_ot_labels:
            # Lifecycles invisible with subprocess invisible
            act_processed = act.split(parameters["LC_DELIMITER"])[0]
            act_processed = f"{act_processed} -> sub"
            ot_hidden = hidden_labels_to_ot[act]
            if ot_hidden.startswith(NAMESPACE_SUBPROCESS):
                act_processed = f"{act_processed} -> sub"
            elif ot_hidden.startswith(NAMESPACE_DEVICES):
                act_processed = f"{act_processed} -> dev"
            elif ot_hidden.startswith(NAMESPACE_RESOURCES):
                act_processed = f"{act_processed} -> res"
            else:
                to_be_removed = NAMESPACE_WORKFLOW + ":"
                act_processed = f"{act_processed} <-> {ot_hidden.removeprefix(to_be_removed)}"
        act_key = act.split(parameters["LC_DELIMITER"])[0]
        if act_key not in activities_to_abstraction:
            activities_to_abstraction[act_key] = {OLD: {act},
                                                  NEW: {act_processed},
                                                  MAPPING: {act: act_processed}}
        else:
            activities_to_abstraction[act_key][OLD].add(act)
            activities_to_abstraction[act_key][NEW].add(act_processed)
            activities_to_abstraction[act_key][MAPPING][act] = act_processed

    labels_to_ids = {}
    already_added = []
    for act in activities_to_abstraction.keys():
        events = activities_to_abstraction[act][NEW]
        sub_event = f"{act} -> sub"
        if act in events and sub_event in events:
            # Only possible for hidden lifecycle and hidden subprocess
            idn = str(uuid.uuid4())
            for a in activities_to_abstraction[act][OLD]:
                activities_map[a] = idn
            viz.node(idn, label=sub_event, shape="box", style="bold")
        elif len(events) == 1:
            # Everything gets abstracted to single activity
            if len(activities_to_abstraction[act][OLD]) > 1:
                # Multiple old activities get abstracted into single new one
                if all([a in hidden_lc_labels for a in activities_to_abstraction[act][OLD]]):
                    idn = str(uuid.uuid4())
                    for a in activities_to_abstraction[act][OLD]:
                        lc_activities_map[a] = idn
                    activities_map[act] = idn
                    viz.node(idn, label=act, shape="box", style="bold")
                else:
                    # IM aggregations
                    for a in activities_to_abstraction[act][OLD]:
                        label = activities_to_abstraction[act][MAPPING][a]
                        if label not in already_added:
                            idn = str(uuid.uuid4())
                            activities_map[a] = idn
                            labels_to_ids[label] = idn
                            if a in acts_to_new_im:
                                activities_map[label] = idn
                                viz.node(idn, label=label, shape="box3d")
                            else:
                                viz.node(idn, label=label, shape="box")
                            already_added.append(label)
                        else:
                            activities_map[a] = labels_to_ids[label]
            else:
                try:
                    label = activities_to_abstraction[act][MAPPING][act]
                except KeyError:
                    # Special case of lifecycle attribute, but only a single one, so actually no real lifecycle model
                    label = next(iter(activities_to_abstraction[act][NEW]))
                if label not in already_added:
                    idn = str(uuid.uuid4())
                    activities_map[act] = idn
                    labels_to_ids[label] = idn
                    if act in acts_to_new_im:
                        activities_map[label] = idn
                        viz.node(idn, label=label, shape="box3d")
                    else:
                        viz.node(idn, label=label, shape="box")
                    already_added.append(label)
                else:
                    activities_map[act] = labels_to_ids[label]
        else:
            # This activity is completely visible
            for a in activities_to_abstraction[act][OLD]:
                label = activities_to_abstraction[act][MAPPING][a]
                if label not in already_added:
                    idn = str(uuid.uuid4())
                    activities_map[a] = idn
                    labels_to_ids[label] = idn
                    if a in acts_to_new_im:
                        activities_map[label] = idn
                        viz.node(idn, label=label, shape="box3d")
                    else:
                        viz.node(idn, label=label, shape="box")
                    already_added.append(label)
                else:
                    activities_map[a] = labels_to_ids[label]

    # Object Types
    for ot in ocpn["object_types"]:
        if ot in visible_ots and not ot.startswith(NAMESPACE_LIFECYCLE):
            otc = ot_to_color(ot)
            source_places[ot] = str(uuid.uuid4())
            target_places[ot] = str(uuid.uuid4())
            viz.node(source_places[ot], label=" ", shape="circle", style="filled", fillcolor=otc)
            viz.node(target_places[ot], label=" ", shape="circle", style="filled", fillcolor=otc)
            # viz.node(target_places[ot], label=" ", shape="underline", fontcolor=otc)
            # viz.node(str(uuid.uuid4()), label=ot, shape="note", fontcolor=otc)

    for ot in ocpn["petri_nets"]:
        if ot in visible_ots and not ot.startswith(NAMESPACE_LIFECYCLE):
            otc = ot_to_color(ot)
            net, im, fm = ocpn["petri_nets"][ot]
            trans_none_arcs = {}
            none_trans_arcs = {}
            # First find transitions
            if ot in hidden_act_labels:
                aots = hidden_act_labels[ot]
                fragments = {i: ([], set(), []) for i in range(len(aots))}
                for i in range(len(aots)):
                    acts = aots[i][list(aots[i].keys())[0]]
                    transitions = [t for t in net.transitions if t.label in acts]
                    places_aot = [arc.source for t in transitions for arc in t.in_arcs] + [
                        arc.target for t in transitions for arc in t.out_arcs
                    ]
                    # Need only to find SE place SE place and tau transitions in between
                    fragment = set(transitions + places_aot)
                    for j in range(i):
                        if i in agg_hierarchy[ot][j]:
                            fragment = fragment.union(fragments[j][1])
                            if fragment == fragments[j][1] and list(aots[i].keys())[0].split(ABS_DELIMITER)[1] == "xor":
                                entries = fragments[j][0]
                                exits = fragments[j][2]
                                # This is a special case of skipping the lower level process tree with tau transition
                                add_tau_before = \
                                    [in_arc.source for p in entries for in_arc in p.in_arcs if
                                     in_arc.source not in fragment][0]
                                add_place_before = [in_arc.source for in_arc in add_tau_before.in_arcs][0]
                                add_tau_after = \
                                    [out_arc.target for p in exits for out_arc in p.out_arcs if
                                     out_arc.target not in fragment][
                                        0]
                                add_place_after = [out_arc.target for out_arc in add_tau_after.out_arcs][0]
                                fragment = fragment.union(
                                    {add_tau_before, add_place_after, add_place_before, add_place_after})
                    entries = []
                    exits = []
                    queue = [p for p in fragment if type(p) is PetriNet.Place]
                    while queue:
                        # Need only to look for tau transitions and the single entry + single exit place
                        active = queue.pop(0)
                        in_border_count = 0
                        in_fragment_count = 0
                        out_fragment_count = 0
                        out_border_count = 0
                        for arc in active.in_arcs:
                            if arc.source.label is not None and arc.source not in fragment:
                                # Labeled out transition coming in
                                in_border_count += 1
                            elif arc.source.label is None and not all(
                                    [in_arc.source in fragment for in_arc in arc.source.in_arcs]):
                                # Tau transition not in fragment
                                in_border_count += 1
                            elif arc.source.label is None and all(
                                    [in_arc.source in fragment for in_arc in arc.source.in_arcs]):
                                fragment.add(arc.source)
                            elif arc.source.label is not None and arc.source in fragment:
                                in_fragment_count += 1
                        for arc in active.out_arcs:
                            if arc.target.label is not None and arc.target not in fragment:
                                # Labeled out transition going out
                                out_border_count += 1
                            elif arc.target.label is None and not all(
                                    [out_arc.target in fragment for out_arc in arc.target.out_arcs]):
                                # Tau transition not in fragment
                                out_border_count += 1
                            elif arc.target.label is None and all(
                                    [out_arc.target in fragment for out_arc in arc.target.out_arcs]):
                                fragment.add(arc.target)
                            elif arc.target.label is not None and arc.target in fragment:
                                out_fragment_count += 1
                        if in_border_count == 1 and out_border_count == 0:
                            # Single Entry Place found
                            entries.append(active)
                        elif in_border_count == 0 and out_border_count == 1:
                            # Single Exit Place found
                            exits.append(active)
                        elif in_border_count >= 1 and out_border_count >= 1 and in_fragment_count >= 1 and out_fragment_count == 0:
                            # Fused single exit place found
                            exits.append(active)
                        elif in_border_count >= 1 and out_border_count >= 1 and in_fragment_count == 0 and out_fragment_count >= 1:
                            entries.append(active)
                    fragments[i] = (entries, fragment, exits)
                # Build mapping from new activity label to fragment in fragments

                new_act_to_fragment = {act: {
                    OLD: fragments[max(acts_ot_to_aot[ot][act])],
                    NEW: generate_single_sese_fragment(),
                    FUSED_IN: [fragments[max(acts_ot_to_aot[ot][act_in])][0][0] for act_in in
                               set(acts_ot_to_new_im[ot].values())
                               if
                               fragments[max(acts_ot_to_aot[ot][act_in])][0] == fragments[max(acts_ot_to_aot[ot][act])][
                                   0]],
                    FUSED_OUT: [fragments[max(acts_ot_to_aot[ot][act_in])][2][0] for act_in in
                                set(acts_ot_to_new_im[ot].values())
                                if fragments[max(acts_ot_to_aot[ot][act_in])][2] ==
                                fragments[max(acts_ot_to_aot[ot][act])][2]],
                    "aot_id": max(acts_ot_to_aot[ot][act])} for act in
                    set(acts_ot_to_new_im[ot].values())}
                # Have to add new places (transitions were already added before) from IM aggregation
                # Have to take care of fused places
                already_fused_added_in = {}
                already_fused_added_out = {}
                for act, fragment_map in new_act_to_fragment.items():
                    for p, pid in fragment_map[NEW].items():
                        insert_string = f"{act}:{p}"
                        if len(fragment_map[FUSED_IN]) >= 2 and p == ENTRY_PLACE:
                            if fragment_map[FUSED_IN][0] not in already_fused_added_in:
                                places[insert_string] = str(uuid.uuid4())
                                already_fused_added_in[fragment_map[FUSED_IN][0]] = places[insert_string]
                                viz.node(places[insert_string], label=" ", shape="circle", style="filled",
                                         fillcolor=otc)
                                trans_before = list({in_arc.source for entry_place in fragment_map[OLD][0]
                                                     for in_arc in entry_place.in_arcs
                                                     if in_arc.source not in fragment_map[OLD][1]})[0]
                                if trans_before.label is not None:
                                    viz.edge(
                                        activities_map[trans_before.label] if trans_before.label in activities_map else
                                        lc_activities_map[trans_before.label],
                                        places[insert_string] if insert_string in places else
                                        already_fused_added_in[
                                            fragment_map[FUSED_IN][0]], color=otc,
                                        penwidth="1.0")
                                else:
                                    trans_none_arcs[trans_before] = places[
                                        insert_string] if insert_string in places else already_fused_added_in[
                                        fragment_map[FUSED_IN][0]]
                            viz.edge(places[insert_string] if insert_string in places else already_fused_added_in[
                                fragment_map[FUSED_IN][0]], activities_map[act], color=otc,
                                     penwidth="1.0")
                        elif len(fragment_map[FUSED_OUT]) >= 2 and p == EXIT_PLACE:
                            if fragment_map[FUSED_OUT][0] not in already_fused_added_out:
                                places[insert_string] = str(uuid.uuid4())
                                already_fused_added_out[fragment_map[FUSED_OUT][0]] = places[insert_string]
                                viz.node(places[insert_string], label=" ", shape="circle", style="filled",
                                         fillcolor=otc)
                                trans_after = list({out_arc.target for exit_place in fragment_map[OLD][2]
                                                    for out_arc in exit_place.out_arcs
                                                    if out_arc.target not in fragment_map[OLD][1]})[0]
                                if trans_after.label is not None:
                                    viz.edge(places[insert_string] if insert_string in places else
                                             already_fused_added_out[fragment_map[FUSED_OUT][0]], activities_map[
                                                 trans_after.label] if trans_after.label in activities_map else
                                             lc_activities_map[trans_after.label], color=otc,
                                             penwidth="1.0")
                                else:
                                    none_trans_arcs[trans_after] = places[insert_string] if insert_string in places else \
                                        already_fused_added_out[fragment_map[FUSED_OUT][0]]
                            viz.edge(activities_map[act],
                                     places[insert_string] if insert_string in places else already_fused_added_out[
                                         fragment_map[FUSED_OUT][0]], color=otc,
                                     penwidth="1.0")

                        else:
                            places[insert_string] = str(uuid.uuid4())
                            viz.node(places[insert_string], label=" ", shape="circle", style="filled", fillcolor=otc)
                            # Have to connect activities with new places
                            if p == ENTRY_PLACE:
                                viz.edge(places[insert_string], activities_map[act], color=otc,
                                         penwidth="1.0")
                                trans_before = list({in_arc.source for entry_place in fragment_map[OLD][0]
                                                     for in_arc in entry_place.in_arcs
                                                     if in_arc.source not in fragment_map[OLD][1]})[0]
                                if trans_before.label is not None:
                                    viz.edge(activities_map[trans_before.label], places[insert_string], color=otc,
                                             penwidth="1.0")
                                else:
                                    trans_none_arcs[trans_before] = places[insert_string]
                                # aot_entry = hidden_act_labels[ot][fragment_map["aot_id"]]
                                aot_acts = list(acts_ot_to_new_im[ot].keys())
                                for arc in fragment_map[OLD][0][0].out_arcs:
                                    if arc.target.label not in aot_acts and arc.target.label is not None:
                                        viz.edge(places[insert_string], activities_map[arc.target.label], color=otc,
                                                 penwidth="1.0")
                                    elif arc.target.label not in aot_acts and arc.target.label is None:
                                        none_trans_arcs[arc.target] = places[insert_string]
                            elif p == EXIT_PLACE:
                                viz.edge(activities_map[act], places[insert_string], color=otc,
                                         penwidth="1.0")
                                trans_after = list({out_arc.target for exit_place in fragment_map[OLD][2]
                                                    for out_arc in exit_place.out_arcs
                                                    if out_arc.target not in fragment_map[OLD][1]})[0]
                                if trans_after.label is not None:
                                    viz.edge(places[insert_string], activities_map[
                                        trans_after.label] if trans_after.label in activities_map else
                                    lc_activities_map[trans_after.label], color=otc,
                                             penwidth="1.0")
                                else:
                                    none_trans_arcs[trans_after] = places[insert_string]
                                aot_acts = list(acts_ot_to_new_im[ot].keys())
                                for arc in fragment_map[OLD][2][0].in_arcs:
                                    if arc.source.label not in aot_acts and arc.source.label is not None:
                                        viz.edge(activities_map[arc.source.label], places[insert_string], color=otc,
                                                 penwidth="1.0")
                                    elif arc.source.label not in aot_acts and arc.source.label is None:
                                        trans_none_arcs[arc.source] = places[insert_string]
                im_aggregated = {p for i in range(len(fragments)) for p in fragments[i][1]}
                im_entry_places = {p for i in range(len(fragments)) for p in fragments[i][0]}
                im_exit_places = {p for i in range(len(fragments)) for p in fragments[i][2]}
            else:
                im_aggregated = set()
                im_entry_places = set()
                im_exit_places = set()
                new_act_to_fragment = {}

            for place in net.places:
                if place in im:
                    places[place] = source_places[ot]
                elif place in fm:
                    places[place] = target_places[ot]
                else:
                    visible_place = reachability_from_place_tau_only(place, activities_map, lc_activities_map, im, fm)
                    target_transitions = {arc.target for arc in place.out_arcs}
                    source_transitions = {arc.source for arc in place.in_arcs}
                    transition_ids = {activities_map[trans.label] if trans.label in activities_map else
                                      (lc_activities_map[trans.label] if trans.label is not None else str(uuid.uuid4()))
                                      for trans in target_transitions.union(source_transitions) if
                                      trans.label in activities_map or trans.label in lc_activities_map or trans.label is None}
                    if visible_place and place not in im_aggregated and len(transition_ids) > 1:
                        # Don't add invisible places and IM aggregated places
                        places[place] = str(uuid.uuid4())
                        viz.node(places[place], label=" ", shape="circle", style="filled", fillcolor=otc)

            for trans in net.transitions:
                in_visible = len(
                    {places[pltr.source] if pltr.source in places else str(uuid.uuid4()) for pltr in trans.in_arcs if
                     pltr.source in places or pltr.source in im_exit_places}) == len(
                    trans.in_arcs)
                out_visible = len(
                    {places[trpl.target] if trpl.target in places else str(uuid.uuid4()) for trpl in trans.out_arcs if
                     trpl.target in places or trpl.target in im_entry_places}) == len(
                    trans.out_arcs)
                if trans.label is not None and trans.label in activities_map:
                    transition_map[trans] = activities_map[trans.label]
                elif trans.label is not None and trans.label in lc_activities_map:
                    transition_map[trans] = lc_activities_map[trans.label]
                elif in_visible and out_visible and trans not in im_aggregated:
                    # Hidden transitions: only visible, if all its places are visible and it is not part of IM aggregated
                    # SESE structure
                    transition_map[trans] = str(uuid.uuid4())
                    viz.node(transition_map[trans], label=" ", shape="box", style="filled", fillcolor=otc)
                    if trans in trans_none_arcs:
                        viz.edge(transition_map[trans], trans_none_arcs[trans], color=otc, penwidth="1.0")
                    if trans in none_trans_arcs:
                        viz.edge(none_trans_arcs[trans], transition_map[trans], color=otc, penwidth="1.0")

            for arc in net.arcs:
                if type(arc.source) is PetriNet.Place and arc.source in places and arc.target in transition_map:
                    is_double = arc.target.label in ocpn["double_arcs_on_activity"][ot] and \
                                ocpn["double_arcs_on_activity"][ot][arc.target.label]
                    penwidth = "4.0" if is_double else "1.0"
                    viz.edge(places[arc.source], transition_map[arc.target], color=otc, penwidth=penwidth)
                elif type(arc.source) is PetriNet.Transition and arc.target in places and arc.source in transition_map:
                    is_double = arc.source.label in ocpn["double_arcs_on_activity"][ot] and \
                                ocpn["double_arcs_on_activity"][ot][arc.source.label]
                    penwidth = "4.0" if is_double else "1.0"
                    viz.edge(transition_map[arc.source], places[arc.target], color=otc, penwidth=penwidth)
    viz.attr(rankdir=rankdir)
    viz.format = image_format
    return viz


def reachability_from_place_tau_only(place: PetriNet.Place, activities_map, lc_activities_map, im, fm) -> Any:
    # Tau transition will only be invisible, if it is enclosed by invisible transitions, but paths ignore further tau transitions
    queue_out = [place.out_arcs]
    queue_in = [place.in_arcs]
    while queue_out:
        active = queue_out.pop(0)
        for arc in active:
            if arc.target.label in activities_map or arc.target.label in lc_activities_map:
                return True
            elif len([pltr.target for pltr in arc.target.out_arcs if pltr.target in fm]) == 1:
                # Connecting to final place
                return True
            elif arc.target.label is None:
                for out_arc in arc.target.out_arcs:
                    queue_out.append(out_arc.target.out_arcs)
    while queue_in:
        active = queue_in.pop(0)
        for arc in active:
            if arc.source.label in activities_map or arc.source.label in lc_activities_map:
                return True
            elif len([pltr.source for pltr in arc.source.in_arcs if pltr.source in im]) == 1:
                # Connecting to source place
                return True
            elif arc.source.label is None:
                for in_arc in arc.source.in_arcs:
                    queue_in.append(in_arc.source.in_arcs)
    return False


def apply(choice: AnyStr,
          available,
          log,
          hid,
          ar,
          ocpn,
          et,
          at,
          hierarchy) -> Tuple:
    ot, agg, events = available[choice]
    # ot, agg, events, aoi, aot = user_redo(log, hid, ot, agg, events)
    log, hid = ar.repo[agg](log, events, ot)
    viz = overlay(log, ocpn, ar, et, hid)
    file_path = "current.svg"
    ocpn_visualizer.save(viz, file_path)
    return retrieve_redoable(log, at, hid, hierarchy), retrieve_available(log, at, hid, hierarchy)


def redo(choice: AnyStr,
         redoable,
         log,
         hid,
         ar,
         ocpn,
         et,
         at,
         hierarchy) -> Tuple:
    ot, agg, events = redoable[choice]
    ot, agg, events, aoi, aot = user_redo(log, hid, ot, agg, events)
    log, hid = ar.repo[agg](log, events, ot, False, aoi, aot)
    viz = overlay(log, ocpn, ar, et, hid)
    file_path = "current.svg"
    ocpn_visualizer.save(viz, file_path)
    return retrieve_redoable(log, at, hid, hierarchy), retrieve_available(log, at, hid, hierarchy)


def user_redo(log, hid, ot, agg, events) -> Tuple:
    if agg is AvailableAggregations.CAA or agg is AvailableAggregations.CLA:
        aot = get_simple_agg_string(ot, agg)
    else:
        aot = get_complex_agg_string(ot, agg, events)
    history = log[constants.OCEL_OBJECTS_KEY][hid]
    applied = history[constants.OCEL_OVMAP_KEY][HISTORY_CURRENT]
    aots = [log[constants.OCEL_OBJECTS_KEY][aoi][constants.DEFAULT_OBJECT_TYPE] for aoi in applied]
    aoi = [applied[i] for i in range(len(aots)) if aots[i] == aot][0]
    return ot, agg, events, aoi, aot


def export(log) -> None:
    json.dump(log, open("inexa_out.jsonocel", "w"), indent=1, default=json_serial)

