import pm4py
import json
from pm4py.visualization.ocel.ocpn import visualizer as ocpn_visualizer

from inexa import ocpd, AggregationRepository, compute_at, NAMESPACE_WORKFLOW, overlay, retrieve_next

ocel_log = pm4py.read_ocel_json("er_example.jsonocel")
ot_wf = [ot for ot in pm4py.ocel_get_object_types(ocel_log) if ot.startswith(NAMESPACE_WORKFLOW)]
log_wf = pm4py.filter_ocel_object_types(ocel_log, ot_wf)
ocpn = ocpd(log_wf)

ar = AggregationRepository()

# Check replay
te = ocpn['activities_indep']['events']
et = {e: tr for e, tr in [(k, t) for t, eset in te.items() for k in eset]}

at, hierarchy = compute_at(ocel_log, ocpn, ar, te)
hid = ""
pm4py.write_ocel_json(log_wf, "out_er.jsonocel")
with open(f"out_er.jsonocel", 'rb') as outp:
    log = json.load(outp)
    outp.close()

viz = overlay(log, ocpn, ar, et, hid)

# Not aggregated
file_path = "running_example.png"
ocpn_visualizer.save(viz, file_path)

for i in range(4):
    ot, agg, events = retrieve_next(log, at, hid, hierarchy)
    log, hid = ar.repo[agg](log, events, ot)

viz = overlay(log, ocpn, ar, et, hid)
file_path = f"running_example.svg"
ocpn_visualizer.save(viz, file_path)