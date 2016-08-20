------------------------------ MODULE Buffers2 ------------------------------
EXTENDS Naturals, Sequences

CONSTANT DATA, N, CONSUMERS, SEND_DATA(_, _), BUFFERS
VARIABLES buffers, pendingStoreRequest, pendingRemoveRequest

ASSUME /\ \A consumer \in CONSUMERS, data \in DATA : SEND_DATA(consumer, data) \in BOOLEAN
       /\ BUFFERS = 1..2

vars == << buffers, pendingStoreRequest, pendingRemoveRequest >>
NoPendingStoreRequest == CHOOSE v : v \notin DATA
NoPendingRemoveRequest == CHOOSE v : v \notin [consumer: CONSUMERS, buffer: BUFFERS]

TypeInvariant == /\ buffers \in [BUFFERS -> Seq(DATA)]
                 /\ pendingStoreRequest \in DATA \cup {NoPendingStoreRequest}
                 /\ pendingRemoveRequest \in [consumer : CONSUMERS, buffer: BUFFERS]
                    \cup {NoPendingRemoveRequest}

SizeInvariant == \A b \in BUFFERS : Len(buffers[b]) <= N
----
Init == /\ buffers = [b \in BUFFERS |-> << >>]
        /\ pendingStoreRequest = NoPendingStoreRequest
        /\ pendingRemoveRequest = NoPendingRemoveRequest

StoreRequest(d) == /\ pendingStoreRequest = NoPendingStoreRequest
                   /\ pendingStoreRequest' = d
                   /\ UNCHANGED << buffers, pendingRemoveRequest >>
   
RemoveRequest(c, b) == /\ pendingRemoveRequest = NoPendingRemoveRequest
                       /\ pendingRemoveRequest' = [consumer |-> c, buffer |-> b]
                       /\ UNCHANGED << buffers, pendingStoreRequest >>
                   
Store == /\ pendingStoreRequest # NoPendingStoreRequest
         /\ \E buffer \in BUFFERS : Len(buffers[buffer]) < N
         /\ \/ /\ Len(buffers[1]) <= Len(buffers[2])
               /\ buffers' = [buffers EXCEPT ![1] = Append(@, pendingStoreRequest)]
            \/ /\ Len(buffers[1]) > Len(buffers[2])
               /\ buffers' = [buffers EXCEPT ![2] = Append(@, pendingStoreRequest)]
         /\ pendingStoreRequest' = NoPendingStoreRequest
         /\ UNCHANGED << pendingRemoveRequest >>

Remove == /\ pendingRemoveRequest # NoPendingRemoveRequest
          /\ \/ /\ Len(buffers[pendingRemoveRequest.buffer]) > 0
                /\ SEND_DATA(pendingRemoveRequest.consumer,
                   Head(buffers[pendingRemoveRequest.buffer]))
                /\ buffers' = [buffers EXCEPT ![pendingRemoveRequest.buffer] = Tail(@)]
             \/ /\ Len(buffers[pendingRemoveRequest.buffer]) = 0
                /\ UNCHANGED << buffers >>
          /\ pendingRemoveRequest' = NoPendingRemoveRequest
          /\ UNCHANGED pendingStoreRequest

Balance == /\ \E big, small \in BUFFERS :
              /\ Len(buffers[big]) > Len(buffers[small]) + 1
              /\ buffers' = [buffers EXCEPT
                 ![big] = Tail(@),
                 ![small] = Append(@, Head(buffers[big]))]
           /\ UNCHANGED << pendingStoreRequest, pendingRemoveRequest >>

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
\* Last modified Wed Aug 03 21:07:32 ART 2016 by juampi
\* Created Sun Jul 31 23:42:10 ART 2016 by juampi
