------------------------------ MODULE Buffers ------------------------------
EXTENDS Naturals, Sequences

CONSTANT DATA, N, CONSUMERS, SEND_DATA(_, _)
VARIABLES buffers, pendingStoreRequests, pendingRemoveRequests

ASSUME \A consumer \in CONSUMERS, data \in DATA : SEND_DATA(consumer, data) \in BOOLEAN

vars == << buffers, pendingStoreRequests, pendingRemoveRequests >>
BUFFERS == 1..2

TypeInvariant == /\ buffers \in [BUFFERS -> Seq(DATA)]
                 /\ pendingStoreRequests \in Seq(DATA)
                 /\ pendingRemoveRequests \in Seq([consumer : CONSUMERS, buffer: BUFFERS])

SizeInvariant == \A b \in BUFFERS : Len(buffers[b]) <= N

----
Init == /\ buffers = [b \in BUFFERS |-> << >>]
        /\ pendingStoreRequests = << >>
        /\ pendingRemoveRequests = << >>

StoreRequest(d) == /\ pendingStoreRequests' = Append(pendingStoreRequests, d)
                   /\ UNCHANGED << buffers, pendingRemoveRequests >>
   
RemoveRequest(c, b) == /\ pendingRemoveRequests' = Append(pendingRemoveRequests,
                          [consumer |-> c, buffer |-> b])
                       /\ UNCHANGED << buffers, pendingStoreRequests >>
                   
Store == /\ Len(pendingStoreRequests) > 0
         /\ \E buffer \in BUFFERS : Len(buffers[buffer]) < N
         /\ \/ /\ Len(buffers[1]) <= Len(buffers[2])
               /\ buffers' = [buffers EXCEPT ![1] = Append(@, Head(pendingStoreRequests))]
            \/ /\ Len(buffers[1]) > Len(buffers[2])
               /\ buffers' = [buffers EXCEPT ![2] = Append(@, Head(pendingStoreRequests))]
         /\ pendingStoreRequests' = Tail(pendingStoreRequests)
         /\ UNCHANGED << pendingRemoveRequests >>

Remove == /\ Len(pendingRemoveRequests) > 0
          /\ LET request == Head(pendingRemoveRequests) IN
             \/ /\ Len(buffers[request.buffer]) > 0
                /\ SEND_DATA(request.consumer, Head(buffers[request.buffer]))
                /\ buffers' = [buffers EXCEPT ![request.buffer] = Tail(@)]
             \/ /\ Len(buffers[request.buffer]) = 0
                /\ UNCHANGED << buffers >>
          /\ pendingRemoveRequests' = Tail(pendingRemoveRequests)
          /\ UNCHANGED pendingStoreRequests

Balance == /\ \E big, small \in BUFFERS :
              /\ Len(buffers[big]) > Len(buffers[small]) + 1
              /\ buffers' = [buffers EXCEPT
                 ![big] = Tail(@),
                 ![small] = Append(@, Head(buffers[big]))]
           /\ UNCHANGED << pendingStoreRequests, pendingRemoveRequests >>

Next == \/ (\E d \in DATA : StoreRequest(d))
        \/ (\E c \in CONSUMERS, b \in BUFFERS : RemoveRequest(c, b))
        \/ Store
        \/ Remove
        \/ Balance

Spec == Init /\ [][Next]_vars /\ WF_vars(Store) /\ WF_vars(Remove) /\ WF_vars(Balance)
----
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SizeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Aug 01 18:55:07 ART 2016 by juampi
\* Created Sun Jul 31 23:42:10 ART 2016 by juampi
