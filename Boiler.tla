------------------------------- MODULE Boiler -------------------------------
EXTENDS Naturals

CONSTANTS TEMP, PRESSURE, MIN_TEMP, MAX_TEMP, MIN_PRESSURE, MAX_PRESSURE
ASSUME /\ MIN_TEMP \in TEMP
       /\ MAX_TEMP \in TEMP
       /\ MIN_PRESSURE \in PRESSURE
       /\ MAX_PRESSURE \in PRESSURE

VARIABLES temp, pressure, burner, tubing, network

vars == << temp, pressure, burner, tubing, network >>

TypeInvariant == /\ temp \in TEMP
                 /\ pressure \in PRESSURE
                 /\ burner \in {"high", "low"}
                 /\ tubing \in {"open", "closed"}
                 /\ network \in {"open", "closed"}
----
Init == /\ temp \in TEMP /\ temp >= MIN_TEMP /\ temp <= MAX_TEMP
        /\ pressure \in PRESSURE /\ pressure >= MIN_PRESSURE /\ pressure <= MAX_PRESSURE
        /\ burner \in {"high", "low"}
        /\ tubing = "closed"
        /\ network = "closed"

MeasureTemp(t) == /\ temp # t
                  /\ temp' = t
                  /\ UNCHANGED << pressure, burner, tubing, network >>

MeasurePressure(p) == /\ pressure # p
                      /\ pressure' = p
                      /\ UNCHANGED << temp, burner, tubing, network >>

IncreaseBurner == /\ burner = "low"
                  /\ temp < MIN_TEMP
                  /\ burner' = "high"
                  /\ UNCHANGED << temp, pressure, tubing, network >>

DecreaseBurner == /\ burner = "high"
                  /\ temp > MAX_TEMP
                  /\ burner' = "low"
                  /\ UNCHANGED << temp, pressure, tubing, network >>

OpenTubing == /\ tubing = "closed"
              /\ pressure > MAX_PRESSURE
              /\ tubing' = "open"
              /\ UNCHANGED << temp, pressure, burner, network >>

CloseTubing == /\ tubing = "open"
               /\ pressure <= MAX_PRESSURE
               /\ tubing' = "closed"
               /\ UNCHANGED << temp, pressure, burner, network >>

OpenNetwork == /\ network = "closed"
               /\ pressure < MIN_PRESSURE
               /\ network' = "open"
               /\ UNCHANGED << temp, pressure, burner, tubing >>

CloseNetwork == /\ network = "open"
                /\ pressure >= MIN_PRESSURE
                /\ network' = "closed"
                /\ UNCHANGED << temp, pressure, burner, tubing >>

Next == \/ (\E t \in TEMP : MeasureTemp(t))
        \/ (\E p \in PRESSURE : MeasurePressure(p))
        \/ IncreaseBurner
        \/ DecreaseBurner
        \/ OpenTubing
        \/ CloseTubing
        \/ OpenNetwork
        \/ CloseNetwork

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(IncreaseBurner \/ DecreaseBurner)
        /\ WF_vars(OpenTubing \/ CloseTubing)
        /\ WF_vars(OpenNetwork \/ CloseNetwork)
----
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Aug 01 12:23:51 ART 2016 by juampi
\* Created Mon Aug 01 11:39:42 ART 2016 by juampi
