----------------------------- MODULE Webserver -----------------------------
CONSTANT USER, PASSWORD, URL, HTML, GET_HTML(_), SEND_HTML(_, _), AUTHENTICATE(_, _), IS_AUTHORIZED(_, _), SEND_ERROR(_)
ASSUME /\ \A user \in USER, pass \in PASSWORD : AUTHENTICATE(user, pass) \in BOOLEAN
       /\ \A user \in USER, url \in URL : IS_AUTHORIZED(user, url) \in BOOLEAN
       /\ \A url \in URL : GET_HTML(url) \in HTML
       /\ \A user \in USER, html \in HTML : SEND_HTML(user, html) \in BOOLEAN

VARIABLES pendingHtmlRequests, pendingSessionRequests, sessions, connections

vars == << pendingHtmlRequests, pendingSessionRequests, sessions, connections >>

TypeInvariant == /\ pendingHtmlRequests \in SUBSET [user: USER, url: URL]
                 /\ sessions \in SUBSET USER
                 /\ connections \in SUBSET USER
----------------------------------------------------------------------------
Init == /\ pendingHtmlRequests = {}
        /\ pendingSessionRequests = {}
        /\ sessions = {}
        /\ connections = {}

RequestHTML(user, url) == /\ pendingHtmlRequests' = pendingHtmlRequests \union {[user |-> user, url |-> url]}
                          /\ UNCHANGED << pendingSessionRequests, sessions >>

RequestSession(user, pass) == /\ pendingSessionRequests' = pendingSessionRequests \union {[user |-> user, pass |-> pass]}
                              /\ UNCHANGED << pendingHtmlRequests, sessions >>

Respond(r) == \/ /\ IS_AUTHORIZED(r.user, r.url)
                 /\ SEND_HTML(r.user, GET_HTML(r.url))
                 /\ pendingHtmlRequests' = pendingHtmlRequests \ {r}
                 /\ UNCHANGED << pendingSessionRequests, sessions >>
              \/ /\ \lnot IS_AUTHORIZED(r.user, r.url)
                 /\ SEND_ERROR(r.user)
                 /\ UNCHANGED vars

ProcessSessionRequest(r) == \/ /\ AUTHENTICATE(r.user, r.pass)
                               /\ sessions' = sessions \cup {r.user}
                               /\ pendingSessionRequests' = pendingSessionRequests \ {r}
                               /\ UNCHANGED << pendingHtmlRequests >>
                            \/ /\ \lnot AUTHENTICATE(r.user, r.pass)
                               /\ pendingSessionRequests' = pendingSessionRequests \ {r}
                               /\ UNCHANGED << pendingHtmlRequests, sessions >>

DropConnection(c) == /\ connections' = connections \ {c}
                     /\ UNCHANGED << pendingHtmlRequests, pendingSessionRequests, sessions >>

Next == \/ (\E user \in USER, url \in URL : RequestHTML(user, url))
        \/ (\E r \in pendingHtmlRequests : Respond(r))
        \/ (\E user \in USER, pass \in PASSWORD : RequestSession(user, pass))
        \/ (\E r \in pendingSessionRequests : ProcessSessionRequest(r))

Spec == /\ Init
        /\ [][Next]_vars
        /\ (\A r \in pendingHtmlRequests : WF_vars(Respond(r)))
        /\ (\A r \in pendingSessionRequests : WF_vars(ProcessSessionRequest(r)))
        /\ (\A c \in connections : WF_vars(DropConnection(c)))
----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Sat Aug 20 20:07:20 ART 2016 by juampi
\* Created Sun Jul 31 13:04:28 ART 2016 by juampi
