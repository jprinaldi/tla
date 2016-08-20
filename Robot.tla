------------------------------ MODULE Robot ------------------------------
EXTENDS Naturals

CONSTANTS TEMP, MAXTEMP

ASSUME MAXTEMP \in TEMP

VARIABLES sprinkler, engine, followPending, returnPending, stopPending

vars == << sprinkler, engine, followPending, returnPending, stopPending >>

TypeInvariant == /\ sprinkler \in {"on", "off"}
                 /\ engine \in {"following", "returning", "stopped"}
                 /\ followPending \in {0, 1}
                 /\ returnPending \in {0, 1}
                 /\ stopPending \in {0, 1}
----
Init == /\ sprinkler = "off"
        /\ engine = "stopped"
        /\ followPending = 0
        /\ returnPending = 0
        /\ stopPending = 0

ReachRightEnd == /\ returnPending' = 1
                 /\ UNCHANGED << sprinkler, engine, followPending, stopPending >>

ReachLeftEnd == /\ stopPending' = 1
                /\ UNCHANGED << sprinkler, engine, followPending, returnPending >>

MeasureTemp(t) == /\ \/ /\ t > MAXTEMP
                        /\ engine # "following"
                        /\ followPending' = 1
                        /\ UNCHANGED << returnPending, stopPending >>
                     \/ /\ t <= MAXTEMP
                        /\ engine = "following"
                        /\ returnPending' = 1
                        /\ UNCHANGED << followPending, stopPending >>
                  /\ UNCHANGED << sprinkler, engine >>

Follow == /\ followPending = 1
          /\ sprinkler' = "on"
          /\ engine' = "following"
          /\ followPending' = 0
          /\ UNCHANGED << returnPending, stopPending >>

Return == /\ returnPending = 1
          /\ sprinkler' = "off"
          /\ engine' = "returning"
          /\ returnPending' = 0
          /\ UNCHANGED << followPending, stopPending >>

Stop == /\ stopPending = 1
        /\ engine' = "stopped"
        /\ stopPending' = 0
        /\ UNCHANGED << sprinkler, followPending, returnPending >>

Next == \/ ReachRightEnd
        \/ ReachLeftEnd
        \/ \E t \in TEMP : MeasureTemp(t)
        \/ Follow
        \/ Return
        \/ Stop

Spec == Init /\ [][Next]_vars /\ WF_vars(Follow) /\ WF_vars(Return) /\ WF_vars(Stop)
----
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Sat Aug 20 20:08:24 ART 2016 by juampi
\* Created Fri Aug 05 17:17:26 ART 2016 by juampi
