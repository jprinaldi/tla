-------------------------------- MODULE Lamp --------------------------------
VARIABLES
  on, \* Represents whether the lamp is on (TRUE) or off (FALSE)
  onPending, \* Represents whether the lamp is waiting to be turned on
  offPending \* Represents whether the lamp is waiting to be turned off

vars == << on, onPending, offPending >>

TypeInvariant == on \in BOOLEAN /\ (~onPending \/ ~offPending)
----
Init == /\ on \in BOOLEAN
        /\ onPending = FALSE
        /\ offPending = FALSE

PressButton == \/ /\ ~on
                  /\ onPending' = TRUE
                  /\ UNCHANGED << on, offPending >>
               \/ /\ on
                  /\ offPending' = TRUE
                  /\ UNCHANGED << on, onPending >>

TurnOn == /\ onPending
          /\ on' = TRUE
          /\ onPending' = FALSE
          /\ UNCHANGED offPending

TurnOff == /\ offPending
           /\ on' = FALSE
           /\ offPending' = FALSE
           /\ UNCHANGED onPending

Next == \/ PressButton
        \/ TurnOn
        \/ TurnOff

Spec == Init /\ [][Next]_vars /\ WF_vars(TurnOn) /\ WF_vars(TurnOff)
----
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Sat Aug 20 20:11:01 ART 2016 by juampi
\* Created Thu Jul 14 20:48:46 ART 2016 by juampi
