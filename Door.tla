-------------------------------- MODULE Door --------------------------------
VARIABLES
  now,
  limit,
  time,
  running,
  open, \* Represents whether the door is open (TRUE) or not (closed, FALSE)
  openPending, \* Represents whether the door is waiting to be opened
  closePending \* Represents whther the door is waiting to be closed

vars == << open, openPending, closePending >>

INSTANCE Timer WITH InitialLimit <- 3

TypeInvariant == /\ open \in BOOLEAN
                 /\ openPending \in BOOLEAN
                 /\ closePending \in BOOLEAN
                 /\ (~openPending \/ ~closePending)
----
Init == /\ open \in BOOLEAN
        /\ openPending = FALSE
        /\ closePending = FALSE

StepOnSignal == /\ ~open
                /\ openPending' = TRUE
                /\ UNCHANGED << open, closePending >>

StepOffSignal == /\ open
                 /\ Start
                 /\ UNCHANGED << open, openPending >>

PrepareClose == /\ Timeout
                /\ closePending' = TRUE
                /\ UNCHANGED << open, openPending >>

Open == /\ openPending
        /\ openPending' = FALSE
        /\ open' = TRUE
        /\ UNCHANGED << closePending >>

Close == /\ closePending
         /\ closePending' = FALSE
         /\ open' = FALSE
         /\ UNCHANGED << openPending >>

Next == \/ StepOnSignal
        \/ StepOffSignal
        \/ Open
        \/ PrepareClose
        \/ Close

Spec == Init /\ [][Next]_vars /\ WF_vars(Open) /\ WF_vars(Close)
----
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Sat Aug 20 20:09:54 ART 2016 by juampi
\* Created Fri Jul 15 08:31:18 ART 2016 by juampi
