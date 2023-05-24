# Assumes the index.txt with xes.yaml files from Zenodo in the same directory

import uuid
from typing import List, Any

import pm4py
import json
from inexa import OCEL_ACT, EXTERNAL, LC_DELIMITER, OCEL_EVENTS, initialize, retrieve_redoable, retrieve_available, apply, redo, export

from yaml import load_all, FullLoader
import json

from datetime import date, datetime

CPEE_INSTANCE_UUID = 'CPEE-INSTANCE-UUID'

CPEE_RAW = 'raw'
CPEE_STATE = "CPEE-STATE"


def json_serial(obj):
    """JSON serializer for objects not serializable by default json code"""

    if isinstance(obj, (datetime, date)):
        return obj.isoformat()
    raise TypeError("Type %s not serializable" % type(obj))


OCEL_GLOBAL = "ocel:global-log"
OCEL_VERSION = "ocel:version"
OCEL_VERSION = "ocel:version"
OCEL_ORDERING = "ocel:ordering"
OCEL_ATTN = "ocel:attribute-names"
OCEL_OBJT = "ocel:object-types"
OCEL_GE = "ocel:global-event"
OCEL_GO = "ocel:global-object"
OCEL_ACT = "ocel:activity"
OCEL_TYPE = "ocel:type"
OCEL_EVENTS = "ocel:events"
OCEL_OBJECTS = "ocel:objects"
OCEL_TIME = "ocel:timestamp"
OCEL_OMAP = "ocel:omap"
OCEL_VMAP = "ocel:vmap"
OCEL_OVMAP = "ocel:ovmap"
OCEL_NA = "__INVALID__"

PATH_PREFIX = './data/'
CONCEPT_INSTANCE = 'concept:instance'
CONCEPT_NAME = 'concept:name'
CONCEPT_ENDPOINT = 'concept:endpoint'
ID = 'id:id'
CPEEID = 'cpee:uuid'
CPEE_ACT_ID = "cpee:activity_uuid"
DATASTREAM = "stream"
DATASTREAM_TO = "stream:to"
ACTIVITY_TO_INSTANCE = "act:instance"
XES_DATASTREAM = "stream:datastream"
XES_DATACONTEXT = "stream:datacontext"
XES_DATASTREAM_NAME = "stream:name"
XES_DATASTREAM_SOURCE = "stream:source"
LIFECYCLE = 'lifecycle:transition'
CPEE_LIFECYCLE = 'cpee:lifecycle:transition'
CPEE_INSTANTIATION = "task/instantiation"
CPEE_RECEIVING = "activity/receiving"
SUB_ROOT = "sub:root"
DATA = 'data'
TIME = 'time:timestamp'
ROOT = 'root'
EVENT = 'event'
DUMMY = ''
EXTERNAL = "external"
NA = "NA"
DICT_TO_LIST = "list"
NAMESPACE_SUBPROCESS = "workflow:sub"
NAMESPACE_LIFECYCLE = "workflow:lc"
NAMESPACE_DEVICES = "workflow:devices"
NAMESPACE_RESOURCES = "workflow:resources"
NAMESPACE_WORKFLOW = "workflow"
CPEE_TIME_STRING = "%Y-%m-%dT%H:%M:%S.%f"
LC_DELIMITER = "§"


class Node:
    def __init__(self, indented_line):
        self.children = []
        self.level = len(indented_line) - len(indented_line.lstrip())
        s = indented_line.strip().split('(')
        self.ot = s[0].strip()
        self.oid = s[1].split(')')[0]

    def add_children(self, nodes, log, data, sub, fail):
        childlevel = nodes[0].level
        while nodes:
            node = nodes.pop(0)
            if node.level == childlevel:  # add node as a child
                self.children.append(node)
                try:
                    temp_trace = read_trace(node.oid)
                    # sub[node.oid] = [temp_trace[0], None]
                    # sub[node.oid][1] = self.ot
                    temp_trace = temp_trace[1:]
                    for event in temp_trace:
                        append_event(self.ot, node.ot, self.oid, node.oid, event, log, ots, data, sub)
                except FileNotFoundError:
                    print(f"Could not read {node.oid}.\n")
                    fail.append(node.oid)
            elif node.level > childlevel:  # add nodes as grandchildren of the last child
                nodes.insert(0, node)
                self.children[-1].add_children(nodes, log_final, data, sub, fail)
            elif node.level <= self.level:  # this node is a sibling, no more children
                nodes.insert(0, node)
                return
            pass

    def as_dict(self):
        if len(self.children) > 1:
            return {self.oid: [node.as_dict() for node in self.children]}
        elif len(self.children) == 1:
            return {self.oid: self.children[0].as_dict()}
        else:
            return self.oid


def read_trace(uuid) -> List[Any]:
    with open(f'{PATH_PREFIX}{uuid}.xes.yaml') as f:
        temp_trace = load_all(f, Loader=FullLoader)
        temp_trace = [i for i in temp_trace]
    return temp_trace


def append_event(ot_parent, ot_child, oid_parent, oid_child, event, log, e_ots, e_data, sub):
    if event[EVENT][CPEE_LIFECYCLE] == "stream/data":
        if XES_DATASTREAM in event[EVENT]:
            data_id = str(uuid.uuid4())
            e_data[DATASTREAM][data_id] = event[EVENT][XES_DATASTREAM]
            log[XES_DATASTREAM].append(data_id)
            if str(event[EVENT][XES_DATASTREAM]).find("context") != -1:
                e_data[DATASTREAM_TO][data_id] = "TODO"
            else:
                # Datastream events without context pertain to the trace
                if oid_child in e_data[DATASTREAM_TO][NAMESPACE_SUBPROCESS]:
                    # Subprocess assigned
                    e_data[DATASTREAM_TO][NAMESPACE_SUBPROCESS][oid_child].append(data_id)
                else:
                    e_data[DATASTREAM_TO][NAMESPACE_SUBPROCESS][oid_child] = [data_id]
                event_actid = event[EVENT][CPEE_ACT_ID]
                if event_actid in e_data[DATASTREAM_TO][CPEE_ACT_ID]:
                    # Task assigned
                    e_data[DATASTREAM_TO][CPEE_ACT_ID][event_actid].append(data_id)
                else:
                    e_data[DATASTREAM_TO][CPEE_ACT_ID][event_actid] = [data_id]
                # e_data[DATASTREAM_TO][data_id] = [oid_child, event[EVENT][CPEE_ACT_ID]]
            # set_nonoptional(event, log, DATASTREAM)
        else:
            log[XES_DATASTREAM].append(DUMMY)
        if XES_DATACONTEXT in event[EVENT]:
            data_id = str(uuid.uuid4())
            e_data[DATASTREAM][data_id] = event[EVENT][XES_DATACONTEXT]
            log[XES_DATACONTEXT].append(data_id)
            # set_nonoptional(event, log, DATACONTEXT)
        else:
            log[XES_DATACONTEXT].append(DUMMY)
    else:
        log[XES_DATASTREAM].append(DUMMY)
        log[XES_DATACONTEXT].append(DUMMY)
    if DATA in event[EVENT]:
        data_id = str(uuid.uuid4())
        e_data[DATA][data_id] = event[EVENT][DATA]
        log[DATA].append(data_id)
    else:
        log[DATA].append(DUMMY)
    if TIME in event[EVENT]:
        set_attribute(event, log, TIME)
    else:
        return
    set_attribute(event, log, CONCEPT_INSTANCE)
    if CONCEPT_NAME in event[EVENT]:
        set_attribute(event, log, CONCEPT_NAME)
    else:
        log[CONCEPT_NAME].append(EXTERNAL)
    if CONCEPT_ENDPOINT in event[EVENT]:
        set_attribute(event, log, CONCEPT_ENDPOINT)
    else:
        log[CONCEPT_ENDPOINT].append(DUMMY)
    if CPEE_ACT_ID in event[EVENT]:
        set_attribute(event, log, CPEE_ACT_ID)
        if log[CONCEPT_NAME][-1] in e_data[ACTIVITY_TO_INSTANCE]:
            if event[EVENT][CPEE_ACT_ID] in e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]]:
                e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]][event[EVENT][CPEE_ACT_ID]] += 1
            else:
                e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]][event[EVENT][CPEE_ACT_ID]] = 1
        else:
            e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]] = {event[EVENT][CPEE_ACT_ID]: 1}
    else:
        log[CPEE_ACT_ID].append(EXTERNAL)
        if log[CONCEPT_NAME][-1] in e_data[ACTIVITY_TO_INSTANCE]:
            e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]][EXTERNAL] += 1
        else:
            e_data[ACTIVITY_TO_INSTANCE][log[CONCEPT_NAME][-1]] = {EXTERNAL: 1}
    set_attribute(event, log, ID)
    set_attribute(event, log, CPEEID)
    set_attribute(event, log, LIFECYCLE)
    set_attribute(event, log, CPEE_LIFECYCLE)
    # Need to generalize this
    if CPEE_LIFECYCLE in event[EVENT] and event[EVENT][CPEE_LIFECYCLE] == CPEE_INSTANTIATION:
        # Task instantiation logic of CPEE
        oid_instantiate = event[EVENT][CPEE_RAW][CPEE_INSTANCE_UUID]
        log[sub[oid_instantiate]].append(oid_instantiate)
        log[SUB_ROOT].append(ot_child)
        temp_e_ots = e_ots - {sub[oid_instantiate]}
    elif CPEE_LIFECYCLE in event[EVENT] and event[EVENT][CPEE_LIFECYCLE] == CPEE_RECEIVING and CPEE_RAW in event[
        EVENT] and DATA in event[EVENT][CPEE_RAW][0] and CPEE_STATE in event[EVENT][CPEE_RAW][0][DATA]:
        state = event[EVENT][CPEE_RAW][0][DATA].split(CPEE_STATE)[1].split('"')[2]
        if state == "finished":
            oid_instantiated = event[EVENT][CPEE_RAW][0][DATA].split(CPEE_INSTANCE_UUID)[1].split('"')[2]
            # Wait running giving control back to callee logic of CPEE
            # oid_instantiated = subprocess_dict[CPEE_INSTANCE_UUID]
            log[sub[oid_instantiated]].append(oid_instantiated)
            temp_e_ots = e_ots - {sub[oid_instantiated]}
            log[SUB_ROOT].append(ot_child)
            # This is in fact label splitting
            log[CPEE_LIFECYCLE][-1] = "subprocess/receiving"
        else:
            temp_e_ots = e_ots
            log[SUB_ROOT].append(NA)
    # elif CPEE_LIFECYCLE in event[EVENT] and event[EVENT][CPEE_LIFECYCLE] == "activity/receiving" and "concept:endpoint" in event[EVENT] and event[EVENT]["concept:endpoint"] == "https-get://centurio.work/ing/correlators/message/receive/" and "raw" in event[EVENT] and "data" in event[EVENT]["raw"] and "ok" in str(event[EVENT]["raw"]["data"]):
    # Only with domain knowledge possible to set this object id of the signalling subprocess that was forked
    else:
        temp_e_ots = e_ots
        log[SUB_ROOT].append(NA)
    log[ot_child].append(oid_child)
    temp_e_ots = temp_e_ots - set([ot_child, ROOT])
    for t in temp_e_ots:
        log[t].append(DUMMY)


def set_attribute(event, log, key):
    try:
        log[key].append(event[EVENT][key])
    except KeyError:
        log[key].append(NA)


with open(PATH_PREFIX + 'index.txt') as f:
    indented_text = f.read()

    ots = {ot.strip().split('(')[0].strip() for ot in indented_text.splitlines() if ot.strip()}

log_final = {CONCEPT_INSTANCE: [],
             CONCEPT_NAME: [],
             CONCEPT_ENDPOINT: [],
             ID: [],
             CPEEID: [],
             LIFECYCLE: [],
             CPEE_LIFECYCLE: [],
             DATA: [],
             TIME: [],
             ROOT: [],
             XES_DATASTREAM: [],
             XES_DATACONTEXT: [],
             CPEE_ACT_ID: [],
             SUB_ROOT: []}

for ot in ots:
    log_final[ot] = []

data = {DATA: {},
        DATASTREAM: {},
        DATASTREAM_TO: {
            NAMESPACE_SUBPROCESS: {},
            CPEE_ACT_ID: {}
        },
        ACTIVITY_TO_INSTANCE: {}}
subprocesses = {ot.strip().split('(')[1].split(')')[0].strip(): ot.strip().split('(')[0].strip() for ot in
                indented_text.splitlines() if ot.strip()}
fail = []

root = Node(f"{ROOT}({str(uuid.uuid4())})")
root.add_children([Node(line) for line in indented_text.splitlines() if line.strip()], log_final, data, subprocesses,
                  fail)
# keyence_measure_dict = dict({'data_receiver': [{'name': 'message', 'mimetype': 'application/json', 'data': [{'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.32, 'timestamp': '2019-11-14T19:36:20.708+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.33, 'timestamp': '2019-11-14T19:36:20.719+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.34, 'timestamp': '2019-11-14T19:36:20.725+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.35, 'timestamp': '2019-11-14T19:36:20.735+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.36, 'timestamp': '2019-11-14T19:36:20.738+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.37, 'timestamp': '2019-11-14T19:36:20.742+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.38, 'timestamp': '2019-11-14T19:36:20.746+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.41, 'timestamp': '2019-11-14T19:36:20.756+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.43, 'timestamp': '2019-11-14T19:36:20.760+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.46, 'timestamp': '2019-11-14T19:36:20.764+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.51, 'timestamp': '2019-11-14T19:36:20.768+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.56, 'timestamp': '2019-11-14T19:36:20.771+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.62, 'timestamp': '2019-11-14T19:36:20.775+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.68, 'timestamp': '2019-11-14T19:36:20.778+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.73, 'timestamp': '2019-11-14T19:36:20.782+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.79, 'timestamp': '2019-11-14T19:36:20.785+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.85, 'timestamp': '2019-11-14T19:36:20.789+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.91, 'timestamp': '2019-11-14T19:36:20.793+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 15.98, 'timestamp': '2019-11-14T19:36:20.797+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.04, 'timestamp': '2019-11-14T19:36:20.800+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.1, 'timestamp': '2019-11-14T19:36:20.804+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.17, 'timestamp': '2019-11-14T19:36:20.807+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.23, 'timestamp': '2019-11-14T19:36:20.811+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.3, 'timestamp': '2019-11-14T19:36:20.815+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.37, 'timestamp': '2019-11-14T19:36:20.818+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.43, 'timestamp': '2019-11-14T19:36:20.822+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.5, 'timestamp': '2019-11-14T19:36:20.826+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.58, 'timestamp': '2019-11-14T19:36:20.829+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.65, 'timestamp': '2019-11-14T19:36:20.833+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.72, 'timestamp': '2019-11-14T19:36:20.836+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.8, 'timestamp': '2019-11-14T19:36:20.840+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.88, 'timestamp': '2019-11-14T19:36:20.844+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 16.95, 'timestamp': '2019-11-14T19:36:20.848+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.03, 'timestamp': '2019-11-14T19:36:20.851+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.11, 'timestamp': '2019-11-14T19:36:20.855+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.18, 'timestamp': '2019-11-14T19:36:20.858+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.25, 'timestamp': '2019-11-14T19:36:20.862+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.33, 'timestamp': '2019-11-14T19:36:20.865+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.4, 'timestamp': '2019-11-14T19:36:20.869+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.48, 'timestamp': '2019-11-14T19:36:20.873+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.55, 'timestamp': '2019-11-14T19:36:20.876+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.63, 'timestamp': '2019-11-14T19:36:20.880+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.71, 'timestamp': '2019-11-14T19:36:20.885+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.8, 'timestamp': '2019-11-14T19:36:20.889+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.86, 'timestamp': '2019-11-14T19:36:20.893+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.9, 'timestamp': '2019-11-14T19:36:20.897+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.94, 'timestamp': '2019-11-14T19:36:20.901+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 17.97, 'timestamp': '2019-11-14T19:36:20.905+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.0, 'timestamp': '2019-11-14T19:36:20.909+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.06, 'timestamp': '2019-11-14T19:36:20.917+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.1, 'timestamp': '2019-11-14T19:36:20.924+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.15, 'timestamp': '2019-11-14T19:36:20.928+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.18, 'timestamp': '2019-11-14T19:36:20.932+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.26, 'timestamp': '2019-11-14T19:36:20.945+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.3, 'timestamp': '2019-11-14T19:36:20.949+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.33, 'timestamp': '2019-11-14T19:36:20.953+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.35, 'timestamp': '2019-11-14T19:36:20.958+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.38, 'timestamp': '2019-11-14T19:36:20.962+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.4, 'timestamp': '2019-11-14T19:36:20.966+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.42, 'timestamp': '2019-11-14T19:36:20.970+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.44, 'timestamp': '2019-11-14T19:36:20.974+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.46, 'timestamp': '2019-11-14T19:36:20.978+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.47, 'timestamp': '2019-11-14T19:36:20.982+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.49, 'timestamp': '2019-11-14T19:36:20.985+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.51, 'timestamp': '2019-11-14T19:36:20.989+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.52, 'timestamp': '2019-11-14T19:36:20.993+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.54, 'timestamp': '2019-11-14T19:36:20.997+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.56, 'timestamp': '2019-11-14T19:36:21.001+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.57, 'timestamp': '2019-11-14T19:36:21.004+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.59, 'timestamp': '2019-11-14T19:36:21.009+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.6, 'timestamp': '2019-11-14T19:36:21.013+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.61, 'timestamp': '2019-11-14T19:36:21.018+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.63, 'timestamp': '2019-11-14T19:36:21.022+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.64, 'timestamp': '2019-11-14T19:36:21.025+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.65, 'timestamp': '2019-11-14T19:36:21.029+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.66, 'timestamp': '2019-11-14T19:36:21.032+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.67, 'timestamp': '2019-11-14T19:36:21.038+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.68, 'timestamp': '2019-11-14T19:36:21.041+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.69, 'timestamp': '2019-11-14T19:36:21.044+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.7, 'timestamp': '2019-11-14T19:36:21.047+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.71, 'timestamp': '2019-11-14T19:36:21.053+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.72, 'timestamp': '2019-11-14T19:36:21.056+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.73, 'timestamp': '2019-11-14T19:36:21.060+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.74, 'timestamp': '2019-11-14T19:36:21.066+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.75, 'timestamp': '2019-11-14T19:36:21.069+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.76, 'timestamp': '2019-11-14T19:36:21.075+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.77, 'timestamp': '2019-11-14T19:36:21.078+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.78, 'timestamp': '2019-11-14T19:36:21.084+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.79, 'timestamp': '2019-11-14T19:36:21.089+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.8, 'timestamp': '2019-11-14T19:36:21.093+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.81, 'timestamp': '2019-11-14T19:36:21.098+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.82, 'timestamp': '2019-11-14T19:36:21.102+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.83, 'timestamp': '2019-11-14T19:36:21.107+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.84, 'timestamp': '2019-11-14T19:36:21.113+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.85, 'timestamp': '2019-11-14T19:36:21.119+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.87, 'timestamp': '2019-11-14T19:36:21.129+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.88, 'timestamp': '2019-11-14T19:36:21.134+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.89, 'timestamp': '2019-11-14T19:36:21.140+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.9, 'timestamp': '2019-11-14T19:36:21.146+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.91, 'timestamp': '2019-11-14T19:36:21.151+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.92, 'timestamp': '2019-11-14T19:36:21.157+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.93, 'timestamp': '2019-11-14T19:36:21.163+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.94, 'timestamp': '2019-11-14T19:36:21.168+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.95, 'timestamp': '2019-11-14T19:36:21.177+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.96, 'timestamp': '2019-11-14T19:36:21.183+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.97, 'timestamp': '2019-11-14T19:36:21.188+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.98, 'timestamp': '2019-11-14T19:36:21.197+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.99, 'timestamp': '2019-11-14T19:36:21.203+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.0, 'timestamp': '2019-11-14T19:36:21.212+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.01, 'timestamp': '2019-11-14T19:36:21.220+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.02, 'timestamp': '2019-11-14T19:36:21.228+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.03, 'timestamp': '2019-11-14T19:36:21.236+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.04, 'timestamp': '2019-11-14T19:36:21.245+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.05, 'timestamp': '2019-11-14T19:36:21.255+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.06, 'timestamp': '2019-11-14T19:36:21.264+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.07, 'timestamp': '2019-11-14T19:36:21.275+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.08, 'timestamp': '2019-11-14T19:36:21.286+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.09, 'timestamp': '2019-11-14T19:36:21.297+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.1, 'timestamp': '2019-11-14T19:36:21.311+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.11, 'timestamp': '2019-11-14T19:36:21.335+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.12, 'timestamp': '2019-11-14T19:36:21.344+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.13, 'timestamp': '2019-11-14T19:36:21.363+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.14, 'timestamp': '2019-11-14T19:36:21.384+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.15, 'timestamp': '2019-11-14T19:36:21.411+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.16, 'timestamp': '2019-11-14T19:36:21.446+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.17, 'timestamp': '2019-11-14T19:36:21.499+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.16, 'timestamp': '2019-11-14T19:36:22.113+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.15, 'timestamp': '2019-11-14T19:36:22.170+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.14, 'timestamp': '2019-11-14T19:36:22.206+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.13, 'timestamp': '2019-11-14T19:36:22.230+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.12, 'timestamp': '2019-11-14T19:36:22.253+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.11, 'timestamp': '2019-11-14T19:36:22.273+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.1, 'timestamp': '2019-11-14T19:36:22.285+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.09, 'timestamp': '2019-11-14T19:36:22.297+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.08, 'timestamp': '2019-11-14T19:36:22.310+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.07, 'timestamp': '2019-11-14T19:36:22.322+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.06, 'timestamp': '2019-11-14T19:36:22.334+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.05, 'timestamp': '2019-11-14T19:36:22.343+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.04, 'timestamp': '2019-11-14T19:36:22.353+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.03, 'timestamp': '2019-11-14T19:36:22.362+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.02, 'timestamp': '2019-11-14T19:36:22.371+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.01, 'timestamp': '2019-11-14T19:36:22.380+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 19.0, 'timestamp': '2019-11-14T19:36:22.387+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.99, 'timestamp': '2019-11-14T19:36:22.394+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.98, 'timestamp': '2019-11-14T19:36:22.400+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.97, 'timestamp': '2019-11-14T19:36:22.407+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.96, 'timestamp': '2019-11-14T19:36:22.413+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.95, 'timestamp': '2019-11-14T19:36:22.420+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.94, 'timestamp': '2019-11-14T19:36:22.426+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.93, 'timestamp': '2019-11-14T19:36:22.430+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.92, 'timestamp': '2019-11-14T19:36:22.437+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.91, 'timestamp': '2019-11-14T19:36:22.444+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.9, 'timestamp': '2019-11-14T19:36:22.447+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.88, 'timestamp': '2019-11-14T19:36:22.460+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.87, 'timestamp': '2019-11-14T19:36:22.467+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.86, 'timestamp': '2019-11-14T19:36:22.471+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.85, 'timestamp': '2019-11-14T19:36:22.477+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.84, 'timestamp': '2019-11-14T19:36:22.481+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.83, 'timestamp': '2019-11-14T19:36:22.485+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.82, 'timestamp': '2019-11-14T19:36:22.489+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.81, 'timestamp': '2019-11-14T19:36:22.493+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.79, 'timestamp': '2019-11-14T19:36:22.496+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.78, 'timestamp': '2019-11-14T19:36:22.500+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.77, 'timestamp': '2019-11-14T19:36:22.504+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.75, 'timestamp': '2019-11-14T19:36:22.508+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.74, 'timestamp': '2019-11-14T19:36:22.512+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.73, 'timestamp': '2019-11-14T19:36:22.516+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.71, 'timestamp': '2019-11-14T19:36:22.519+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.7, 'timestamp': '2019-11-14T19:36:22.523+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.68, 'timestamp': '2019-11-14T19:36:22.527+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.67, 'timestamp': '2019-11-14T19:36:22.531+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.66, 'timestamp': '2019-11-14T19:36:22.535+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.64, 'timestamp': '2019-11-14T19:36:22.538+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.63, 'timestamp': '2019-11-14T19:36:22.542+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.61, 'timestamp': '2019-11-14T19:36:22.546+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.6, 'timestamp': '2019-11-14T19:36:22.552+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.58, 'timestamp': '2019-11-14T19:36:22.556+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.56, 'timestamp': '2019-11-14T19:36:22.560+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.55, 'timestamp': '2019-11-14T19:36:22.564+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.53, 'timestamp': '2019-11-14T19:36:22.568+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.52, 'timestamp': '2019-11-14T19:36:22.572+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.5, 'timestamp': '2019-11-14T19:36:22.576+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.49, 'timestamp': '2019-11-14T19:36:22.579+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.47, 'timestamp': '2019-11-14T19:36:22.583+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.45, 'timestamp': '2019-11-14T19:36:22.587+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.44, 'timestamp': '2019-11-14T19:36:22.591+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.43, 'timestamp': '2019-11-14T19:36:22.595+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.41, 'timestamp': '2019-11-14T19:36:22.598+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.4, 'timestamp': '2019-11-14T19:36:22.602+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.38, 'timestamp': '2019-11-14T19:36:22.606+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.37, 'timestamp': '2019-11-14T19:36:22.610+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.36, 'timestamp': '2019-11-14T19:36:22.615+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.34, 'timestamp': '2019-11-14T19:36:22.619+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.33, 'timestamp': '2019-11-14T19:36:22.623+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 18.31, 'timestamp': '2019-11-14T19:36:22.626+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 999.99, 'timestamp': '2019-11-14T19:36:22.630+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.47, 'timestamp': '2019-11-14T19:36:23.212+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.48, 'timestamp': '2019-11-14T19:36:23.295+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.47, 'timestamp': '2019-11-14T19:36:23.449+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.46, 'timestamp': '2019-11-14T19:36:23.520+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.45, 'timestamp': '2019-11-14T19:36:23.562+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.44, 'timestamp': '2019-11-14T19:36:23.599+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.43, 'timestamp': '2019-11-14T19:36:23.628+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.42, 'timestamp': '2019-11-14T19:36:23.656+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.41, 'timestamp': '2019-11-14T19:36:23.682+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.4, 'timestamp': '2019-11-14T19:36:23.705+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.39, 'timestamp': '2019-11-14T19:36:23.725+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.38, 'timestamp': '2019-11-14T19:36:23.745+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.37, 'timestamp': '2019-11-14T19:36:23.765+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.36, 'timestamp': '2019-11-14T19:36:23.783+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.35, 'timestamp': '2019-11-14T19:36:23.800+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.34, 'timestamp': '2019-11-14T19:36:23.818+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.33, 'timestamp': '2019-11-14T19:36:23.833+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.32, 'timestamp': '2019-11-14T19:36:23.848+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.31, 'timestamp': '2019-11-14T19:36:23.863+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.3, 'timestamp': '2019-11-14T19:36:23.878+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.29, 'timestamp': '2019-11-14T19:36:23.893+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.28, 'timestamp': '2019-11-14T19:36:23.907+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.27, 'timestamp': '2019-11-14T19:36:23.919+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.26, 'timestamp': '2019-11-14T19:36:23.931+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.25, 'timestamp': '2019-11-14T19:36:23.942+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.24, 'timestamp': '2019-11-14T19:36:23.955+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.23, 'timestamp': '2019-11-14T19:36:23.967+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.22, 'timestamp': '2019-11-14T19:36:23.980+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.21, 'timestamp': '2019-11-14T19:36:23.992+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.2, 'timestamp': '2019-11-14T19:36:24.001+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.19, 'timestamp': '2019-11-14T19:36:24.014+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.18, 'timestamp': '2019-11-14T19:36:24.023+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.17, 'timestamp': '2019-11-14T19:36:24.032+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.16, 'timestamp': '2019-11-14T19:36:24.044+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.15, 'timestamp': '2019-11-14T19:36:24.051+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.14, 'timestamp': '2019-11-14T19:36:24.064+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.13, 'timestamp': '2019-11-14T19:36:24.075+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.12, 'timestamp': '2019-11-14T19:36:24.080+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.11, 'timestamp': '2019-11-14T19:36:24.087+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.1, 'timestamp': '2019-11-14T19:36:24.093+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.09, 'timestamp': '2019-11-14T19:36:24.102+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.08, 'timestamp': '2019-11-14T19:36:24.111+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.07, 'timestamp': '2019-11-14T19:36:24.120+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.06, 'timestamp': '2019-11-14T19:36:24.127+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.05, 'timestamp': '2019-11-14T19:36:24.133+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.04, 'timestamp': '2019-11-14T19:36:24.143+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.03, 'timestamp': '2019-11-14T19:36:24.149+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 8.01, 'timestamp': '2019-11-14T19:36:24.155+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.97, 'timestamp': '2019-11-14T19:36:24.159+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.92, 'timestamp': '2019-11-14T19:36:24.162+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.87, 'timestamp': '2019-11-14T19:36:24.166+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.82, 'timestamp': '2019-11-14T19:36:24.170+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.76, 'timestamp': '2019-11-14T19:36:24.174+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.71, 'timestamp': '2019-11-14T19:36:24.178+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.68, 'timestamp': '2019-11-14T19:36:24.181+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.67, 'timestamp': '2019-11-14T19:36:24.185+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.66, 'timestamp': '2019-11-14T19:36:24.188+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.65, 'timestamp': '2019-11-14T19:36:24.192+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.64, 'timestamp': '2019-11-14T19:36:24.198+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.63, 'timestamp': '2019-11-14T19:36:24.204+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.62, 'timestamp': '2019-11-14T19:36:24.213+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.61, 'timestamp': '2019-11-14T19:36:24.220+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.6, 'timestamp': '2019-11-14T19:36:24.226+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.59, 'timestamp': '2019-11-14T19:36:24.232+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.58, 'timestamp': '2019-11-14T19:36:24.241+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.57, 'timestamp': '2019-11-14T19:36:24.248+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.56, 'timestamp': '2019-11-14T19:36:24.254+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.55, 'timestamp': '2019-11-14T19:36:24.263+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.53, 'timestamp': '2019-11-14T19:36:24.267+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.51, 'timestamp': '2019-11-14T19:36:24.271+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.49, 'timestamp': '2019-11-14T19:36:24.275+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.48, 'timestamp': '2019-11-14T19:36:24.278+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.49, 'timestamp': '2019-11-14T19:36:24.285+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.52, 'timestamp': '2019-11-14T19:36:24.288+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.56, 'timestamp': '2019-11-14T19:36:24.292+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.61, 'timestamp': '2019-11-14T19:36:24.296+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.65, 'timestamp': '2019-11-14T19:36:24.300+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.68, 'timestamp': '2019-11-14T19:36:24.304+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.72, 'timestamp': '2019-11-14T19:36:24.308+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.73, 'timestamp': '2019-11-14T19:36:24.311+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.72, 'timestamp': '2019-11-14T19:36:24.318+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.71, 'timestamp': '2019-11-14T19:36:24.324+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.7, 'timestamp': '2019-11-14T19:36:24.328+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.69, 'timestamp': '2019-11-14T19:36:24.332+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.68, 'timestamp': '2019-11-14T19:36:24.338+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.67, 'timestamp': '2019-11-14T19:36:24.342+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.66, 'timestamp': '2019-11-14T19:36:24.346+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.65, 'timestamp': '2019-11-14T19:36:24.352+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.64, 'timestamp': '2019-11-14T19:36:24.356+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.63, 'timestamp': '2019-11-14T19:36:24.359+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.62, 'timestamp': '2019-11-14T19:36:24.363+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.61, 'timestamp': '2019-11-14T19:36:24.367+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.6, 'timestamp': '2019-11-14T19:36:24.371+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.59, 'timestamp': '2019-11-14T19:36:24.377+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.58, 'timestamp': '2019-11-14T19:36:24.381+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.57, 'timestamp': '2019-11-14T19:36:24.385+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.56, 'timestamp': '2019-11-14T19:36:24.392+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.57, 'timestamp': '2019-11-14T19:36:24.401+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.56, 'timestamp': '2019-11-14T19:36:24.411+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.55, 'timestamp': '2019-11-14T19:36:24.415+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.54, 'timestamp': '2019-11-14T19:36:24.419+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.53, 'timestamp': '2019-11-14T19:36:24.423+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.52, 'timestamp': '2019-11-14T19:36:24.427+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.51, 'timestamp': '2019-11-14T19:36:24.434+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.5, 'timestamp': '2019-11-14T19:36:24.438+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.49, 'timestamp': '2019-11-14T19:36:24.442+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.48, 'timestamp': '2019-11-14T19:36:24.446+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.47, 'timestamp': '2019-11-14T19:36:24.450+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.46, 'timestamp': '2019-11-14T19:36:24.454+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.45, 'timestamp': '2019-11-14T19:36:24.459+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.44, 'timestamp': '2019-11-14T19:36:24.467+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.42, 'timestamp': '2019-11-14T19:36:24.471+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.41, 'timestamp': '2019-11-14T19:36:24.478+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.4, 'timestamp': '2019-11-14T19:36:24.482+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.39, 'timestamp': '2019-11-14T19:36:24.487+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.38, 'timestamp': '2019-11-14T19:36:24.493+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.37, 'timestamp': '2019-11-14T19:36:24.497+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.36, 'timestamp': '2019-11-14T19:36:24.501+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.35, 'timestamp': '2019-11-14T19:36:24.505+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.34, 'timestamp': '2019-11-14T19:36:24.509+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.33, 'timestamp': '2019-11-14T19:36:24.513+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.32, 'timestamp': '2019-11-14T19:36:24.520+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.31, 'timestamp': '2019-11-14T19:36:24.524+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.3, 'timestamp': '2019-11-14T19:36:24.528+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.29, 'timestamp': '2019-11-14T19:36:24.532+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.28, 'timestamp': '2019-11-14T19:36:24.536+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.27, 'timestamp': '2019-11-14T19:36:24.540+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.26, 'timestamp': '2019-11-14T19:36:24.544+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.25, 'timestamp': '2019-11-14T19:36:24.548+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.24, 'timestamp': '2019-11-14T19:36:24.552+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.23, 'timestamp': '2019-11-14T19:36:24.556+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.22, 'timestamp': '2019-11-14T19:36:24.560+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.21, 'timestamp': '2019-11-14T19:36:24.564+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.2, 'timestamp': '2019-11-14T19:36:24.568+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.19, 'timestamp': '2019-11-14T19:36:24.572+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.18, 'timestamp': '2019-11-14T19:36:24.576+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.17, 'timestamp': '2019-11-14T19:36:24.580+01:00', 'meta': {}}, {'ID': 'keyence/measurement', 'source': 'keyence', 'name': 'measurement', 'description': '', 'path': 'measurement', 'value': 7.16, 'timestamp': '2019-11-14T19:36:24.584+01:00', 'meta': {}}]}]})
# microvu_measure_dict = dict({'data_changer': ['qc2', 'qc2_success'], 'data_values': {'qr': '*268MFA466*TZHZE 035', 'qc2': {'Zylinder Ø4,5-B': {'Durchmesser': {'status': 'ok', 'on_scale_from_zero_to_one': 0.6166666666666863}, 'Zylinderform': {'status': 'nok', 'on_scale_from_zero_to_one': 1.16}, 'Rechtwinkligkeit': {'status': 'ok', 'on_scale_from_zero_to_one': 0.4}}, 'Kreis Ø19,2-1': {'Mitte Z': {'status': 'ok', 'on_scale_from_zero_to_one': 0.8620000000000014}, 'Durchmesser': {'status': 'ok', 'on_scale_from_zero_to_one': 0.48999999999998795}}, 'Kreis Ø19,2-2': {'Mitte Z': {'status': 'ok', 'on_scale_from_zero_to_one': 0.8690000000000012}, 'Durchmesser': {'status': 'ok', 'on_scale_from_zero_to_one': 0.41200000000002873}}, 'Zylinder 19,2-CZ': {}, 'Distanz Z9,3': {'Distanz Z': {'status': 'ok', 'on_scale_from_zero_to_one': 0.6039999999999978}}, 'Distanz Z4,8': {'Distanz Z': {'status': 'ok', 'on_scale_from_zero_to_one': 0.47500000000000486}}}, 'qc2_success': False}, 'data_received': None})

result = {}
ocel_json = {}

concepts = list(set(log_final[CONCEPT_NAME]))

# No Datastream in data objects
# {k: v for k,v in data[DATA].items() if str(v).find("point") != -1}

components_from_dataid = {
    k: {
        XES_DATASTREAM_NAME: v[0][XES_DATASTREAM_NAME] if XES_DATASTREAM_NAME in v[0] else NA,
        XES_DATASTREAM_SOURCE: v[1][XES_DATASTREAM_SOURCE] if len(v) > 1 and XES_DATASTREAM_SOURCE in v[1] else NA
    } for k, v in data[DATASTREAM].items()}

components = {
    v[0][XES_DATASTREAM_NAME]: v[1][XES_DATASTREAM_SOURCE]
    for k, v in data[DATASTREAM].items() if XES_DATASTREAM_NAME in v[0]}

components[NA] = None

components_uids = {
    k: str(uuid.uuid4()) for k in components.keys()
}

all_lifecycles = [f"{NAMESPACE_LIFECYCLE}:{i}" for i in concepts]
all_sub = [f"{NAMESPACE_SUBPROCESS}:{i}" for i in ots]
all_comp = [f"{NAMESPACE_DEVICES}:{i}" for i in components_uids.keys()]
all_ots = [DATA, DATASTREAM] + all_lifecycles + all_sub + all_comp

attn = [DATA, CONCEPT_ENDPOINT, CONCEPT_INSTANCE, ID, CPEEID, CPEE_ACT_ID, LIFECYCLE, CPEE_LIFECYCLE, SUB_ROOT]

ocel_json[OCEL_GLOBAL] = {"ocel:version": "0.1",
                          "ocel:ordering": "timestamp",
                          "ocel:attribute-names": attn,
                          "ocel:object-types": all_ots}
ocel_json[OCEL_GE] = {OCEL_ACT: OCEL_NA}
ocel_json[OCEL_GO] = {OCEL_TYPE: OCEL_NA}

# Add all keys to data
for id in log_final[CPEE_ACT_ID]:
    if id not in data[DATASTREAM_TO][CPEE_ACT_ID]:
        data[DATASTREAM_TO][CPEE_ACT_ID][id] = []

lifecycle_counts = {k: log_final[CPEE_ACT_ID].count(k) for k in set(log_final[CPEE_ACT_ID])}

no_lifecycles_all = {k: 0 for k, v in lifecycle_counts.items() if v == 1}
no_lifecycles_real = {}
for k in no_lifecycles_all:
    activities = [act for act, ids in data[ACTIVITY_TO_INSTANCE].items() if k in ids]
    act = activities[0]
    no_lifecycles_all[k] = act
    another = 0
    for aid in data[ACTIVITY_TO_INSTANCE][act]:
        if data[ACTIVITY_TO_INSTANCE][act][aid] > 1:
            another = 1
    if another == 0:
        no_lifecycles_real[k] = act

ocel_json[OCEL_EVENTS] = {
    str(uuid.uuid4()): {
        OCEL_ACT: f"{log_final[CONCEPT_NAME][i]}{LC_DELIMITER}{log_final[CPEE_LIFECYCLE][i]}",
        OCEL_TIME: log_final[TIME][i],
        OCEL_OMAP: [log_final[k][i] for k in list(ots) if log_final[k][i] != ""] + [
            # Lifecycle
            log_final[CPEE_ACT_ID][i]  # if lifecycle_counts[log_final[CPEE_ACT_ID][i]] > 0 else 0
            # Components
        ] + list({components_uids[components_from_dataid[dataid][XES_DATASTREAM_NAME]]
                  for dataid in data[DATASTREAM_TO][CPEE_ACT_ID][log_final[CPEE_ACT_ID][i]]}),
        OCEL_VMAP: {
            k: log_final[k][i]
            for k in attn
            # Only attributes that contain a value
            if log_final[k][i] != DUMMY and log_final[k][i] != NA
        }
    }
    for i in range(len(log_final[CONCEPT_NAME]))
}

external_names = list(
    {e[OCEL_ACT] for i, e in ocel_json[OCEL_EVENTS].items() if e[OCEL_ACT].find(f"{EXTERNAL}{LC_DELIMITER}") == 0})

# Remove dummy 0 object identifier for activity having no lifecycle
event_ids = [(k, v[OCEL_VMAP][CPEE_ACT_ID]) for k, v in ocel_json[OCEL_EVENTS].items() if
             v[OCEL_VMAP][CPEE_ACT_ID] in no_lifecycles_real]
for eid, aid in event_ids:
    ocel_json[OCEL_EVENTS][eid][OCEL_OMAP].remove(aid)

# Ids for data + for lifecycles + for subprocesses
all_oids = list(data.keys()) + list(set(log_final[CPEE_ACT_ID])) + list(subprocesses.keys())

data_objects = {
    k: {
        OCEL_TYPE: DATA,
        OCEL_OVMAP: {DICT_TO_LIST: data[DATA][k]}
    }
    for k in data[DATA].keys()
}

datastream_objects = {
    k: {
        OCEL_TYPE: DATASTREAM,
        OCEL_OVMAP: {DICT_TO_LIST: data[DATASTREAM][k]}
    }
    for k in data[DATASTREAM].keys()
}

lifecycle_objects = {
    k: {
        OCEL_TYPE: f"{NAMESPACE_LIFECYCLE}:{log_final[CONCEPT_NAME][i]}",
        OCEL_OVMAP: {}
    }
    for k, i in zip(log_final[CPEE_ACT_ID], range(len(log_final[CPEE_ACT_ID])))
    if k not in no_lifecycles_real
}

subprocess_objects = {
    k: {
        OCEL_TYPE: f"{NAMESPACE_SUBPROCESS}:{v}",
        OCEL_OVMAP: {}
    }
    for k, v in subprocesses.items()
}

component_objects = {
    v: {
        OCEL_TYPE: f"{NAMESPACE_DEVICES}:{k}",
        OCEL_OVMAP: {}
    }
    for k, v in components_uids.items()
}

ocel_json[OCEL_OBJECTS] = {**data_objects, **datastream_objects, **lifecycle_objects, **subprocess_objects,
                           **component_objects}

json.dump(ocel_json, open(PATH_PREFIX + "out.jsonocel", "w"), indent=1, default=json_serial)


# Real-World Example from Evaluation Section
ocel_log = pm4py.read_ocel_json(PATH_PREFIX + "out.jsonocel")
with open(f"{PATH_PREFIX}out.jsonocel", 'rb') as outp:
    log = json.load(outp)

external_names = list({e[OCEL_ACT] for i, e in log[OCEL_EVENTS].items()
                               if e[OCEL_ACT].find(f"{EXTERNAL}{LC_DELIMITER}") == 0})
ots = [ot for ot in pm4py.ocel_get_object_types(ocel_log) if ot != "workflow:lifecycle:external"]
ocel_sub = pm4py.filter_ocel_object_types(ocel_log, ots)
ocel_sub_ext = pm4py.filter_ocel_event_attribute(ocel_sub, OCEL_ACT, external_names, positive=False)

log, ocpn, at, et, te, hierarchy, hid, viz, ar = initialize(ocel_sub_ext, log)

redoable = retrieve_redoable(log, at, hid, hierarchy)
available = retrieve_available(log, at, hid, hierarchy)

available_choice = 'workflow:sub:- Turm Batch Processing V2'
redoable, available = apply(available_choice, available, log, hid, ar, ocpn, et, at, hierarchy)

# Further choices from redoable can be redone in the following way
redo_choice = 'workflow:sub:Turm Single wr08'
redoable, available = redo(redo_choice, redoable, log, hid, ar, ocpn, et, at, hierarchy)

export(log)


