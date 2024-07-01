------------------------------ MODULE version14 ---------------------------

EXTENDS  Sequences,Naturals,TLC,FiniteSets

CONSTANTS any

VARIABLES depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack, _pc

vars == << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack, _pc >>

upperbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : n >= m

lowerbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : m >= n

Broker == 
          LET Broker_start == 1 IN 
           LET Broker_end == 1 IN
               Broker_start .. Broker_end

Publisher == 
             LET Publisher_start == upperbound(Broker) + 1 IN 
              LET Publisher_end == upperbound(Broker) + 1 IN
                  Publisher_start .. Publisher_end

Subscriber == 
              LET Subscriber_start == upperbound(Publisher) + 1 IN 
               LET Subscriber_end == upperbound(Publisher) + 1 IN
                   Subscriber_start .. Subscriber_end

attaque == 
           LET attaque_start == upperbound(Subscriber) + 1 IN 
            LET attaque_end == upperbound(Subscriber) + 1 IN
                attaque_start .. attaque_end

ProcSet == Broker \cup Publisher \cup Subscriber \cup attaque

send(ch,msg) == [network EXCEPT ![ch] = Append(@, msg)]

Init == 
    /\ depth = 0
    /\ cp = any
    /\ network = [p \in ((Broker \cup Publisher) \cup Subscriber) |-> <<>>]
    /\ activeClients = {}
    /\ sessionClients = {}
    /\ idtopic = 1
    /\ RetainedMessages = {}
    /\ pk = FALSE
    /\ Topics = {"A", "B", "C"}
    /\ TopicPool = [t \in Topics |-> {}]
    /\ _Broker_data = [self \in Broker |-> [ self |-> self, parentID |-> 0, Name|->"Broker", rules|->0, status|->0, statusRecord|->0, wait_REL|->{}, wait_COMP|->{}]]

    /\ _Publisher_data = [self \in Publisher |-> [ self |-> self, parentID |-> 0, Name|->"Publisher", CONNSUCC|->FALSE, PUBSUCC|->FALSE, BrokerID|->1]]

    /\ _Subscriber_data = [self \in Subscriber |-> [ self |-> self, parentID |-> 0, Name|->"Subscriber", rules|->0, BrokerID|->1, SUBSUCC|->FALSE, CONNSUCC|->FALSE, PUBRECE|->FALSE, UNSUBSUCC|->FALSE, INJ2|->FALSE]]

    /\ _attaque_data = [self \in attaque |-> [ self |-> self, parentID |-> 0, Name|->"attaque", BrokerID|->1, OBS1|->FALSE, INJ|->FALSE, pk|->1, OBS2|->FALSE]]

    /\ _stack = [self \in ProcSet |-> << >>]
    /\ _pc = [self \in ProcSet |-> CASE self \in Broker -> "listen"
                         []self \in Publisher -> "PubStart"
                         []self \in Subscriber -> "Sub_start"
                         []self \in attaque -> "sessionconn"]

Push(s,e) == e \circ s 

Lbl_1(self) == 
               /\ _pc[self] = "Lbl_1"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_2(self) == 
               /\ _pc[self] = "Lbl_2"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (Len(network[self]) > 0)
                        /\ LET packet == Head(network[self]) IN
                           \/ /\ (packet.type = "PUBREL")
                                 /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                    LET _newhead == Head(_stack[self]) IN
                                    LET __newhead == [_newhead EXCEPT !.PUBRECE = TRUE ] IN
                                    LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                    LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                    LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                    /\ network' = __network
                                    /\ _stack' = ___stack
                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                           \/ /\ ~((packet.type = "PUBREL"))
                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_3(self) == 
               /\ _pc[self] = "Lbl_3"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREL", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_4(self) == 
               /\ _pc[self] = "Lbl_4"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                           /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                  \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_5(self) == 
               /\ _pc[self] = "Lbl_5"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead1 == Head(_stack[self]) IN
                                LET _newHead1 == [newHead1 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead1>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead2 == Head(_stack[self]) IN
                                              LET _newHead2 == [newHead2 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead2>>) ] IN
                                              LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, topic |-> Head(___stack[self]).pkt.topic, QoS |-> 2, retain |-> 0, payload |-> "bonjour", responsetopic |-> Head(___stack[self]).pkt.topic, correlationdata |-> "bonjour"]) IN
                                              LET __newhead == Head(___stack[self]) IN
                                              LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                              LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                              LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                              /\ IF Head(_____stack[self]).idS_sub # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                    ELSE
                                                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_6(self) == 
               /\ _pc[self] = "Lbl_6"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.willtopic] # {})
                           /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                  \/ /\ ~((TopicPool[Head(_stack[self]).pkt.willtopic] # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_7(self) == 
               /\ _pc[self] = "Lbl_7"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.willtopic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead3 == Head(_stack[self]) IN
                                LET _newHead3 == [newHead3 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.willtopic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead3>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead4 == Head(_stack[self]) IN
                                              LET _newHead4 == [newHead4 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead4>>) ] IN
                                              /\ \/ /\ (Head(___stack[self]).pkt.keepalive = 0)
                                                    /\ LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, topic |-> Head(___stack[self]).pkt.willtopic, QoS |-> Head(___stack[self]).pkt.willqos, retain |-> Head(___stack[self]).pkt.willretain, payload |-> Head(___stack[self]).pkt.willpayload, responsetopic |-> Head(___stack[self]).pkt.willtopic, correlationdata |-> Head(___stack[self]).pkt.willpayload]) IN
                                                       LET _pk == TRUE IN
                                                       LET __newhead == Head(___stack[self]) IN
                                                       LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                                       LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                                       LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                                       /\ IF Head(_____stack[self]).idS_sub # {}
                                                             THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                                                     /\ _stack' = _____stack
                                                                     /\ network' = _network
                                                                     /\ pk' = _pk
                                                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                             ELSE
                                                                     /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                                     /\ _stack' = _____stack
                                                                     /\ network' = _network
                                                                     /\ pk' = _pk
                                                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                 \/ /\ ~((Head(___stack[self]).pkt.keepalive = 0))
                                                       /\ LET __newhead == Head(___stack[self]) IN
                                                          LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                                          LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                                          LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                                          /\ IF Head(_____stack[self]).idS_sub # {}
                                                                THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                                                        /\ _stack' = _____stack
                                                                        /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                                ELSE
                                                                        /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                                        /\ _stack' = _____stack
                                                                        /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_8(self) == 
               /\ _pc[self] = "Lbl_8"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                           /\ _pc' = [_pc EXCEPT ![self] = "Lbl_9"]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                  \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_9(self) == 
               /\ _pc[self] = "Lbl_9"
               /\ (cp = any \/ cp = self)
               /\ IF RetainedMessages # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead5 == Head(_stack[self]) IN
                                LET _newHead5 == [newHead5 EXCEPT !.idS_sub = RetainedMessages ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead5>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_9"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead6 == Head(_stack[self]) IN
                                              LET _newHead6 == [newHead6 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead6>>) ] IN
                                              /\ \/ /\ (Head(___stack[self]).sub = Head(___stack[self]).pkt.topic)
                                                    /\ LET _network == send(Head(___stack[self]).pkt.sender, [type |-> "PUBLISH", sender |-> self, topic |-> Head(___stack[self]).pkt.topic, QoS |-> Head(___stack[self]).pkt.QoS, retain |-> 0, payload |-> "bonjour", responsetopic |-> Head(___stack[self]).pkt.topic, CorrelationData |-> "bonjour"]) IN
                                                       LET __newhead == Head(___stack[self]) IN
                                                       LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                                       LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                                       LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                                       /\ IF Head(_____stack[self]).idS_sub # {}
                                                             THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_9"]
                                                                     /\ _stack' = _____stack
                                                                     /\ network' = _network
                                                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                             ELSE
                                                                     /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                                     /\ _stack' = _____stack
                                                                     /\ network' = _network
                                                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                 \/ /\ ~((Head(___stack[self]).sub = Head(___stack[self]).pkt.topic))
                                                       /\ LET __newhead == Head(___stack[self]) IN
                                                          LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                                          LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                                          LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                                          /\ IF Head(_____stack[self]).idS_sub # {}
                                                                THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_9"]
                                                                        /\ _stack' = _____stack
                                                                        /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                                ELSE
                                                                        /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                                        /\ _stack' = _____stack
                                                                        /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_10(self) == 
                /\ _pc[self] = "Lbl_10"
                /\ (cp = any \/ cp = self)
                /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                         /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PINGRESP", sender |-> self]) IN
                            /\ network' = _network
                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                            /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                   \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
cqos2(self) == 
               /\ _pc[self] = "cqos2"
               /\ (cp = any \/ cp = self)
               /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 2, retain |-> 0, payload |-> "bonjour", responsetopic |-> "A", correlationdata |-> "bonjour"]) IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "waitPUB2"]
                  /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
waitPUB2(self) == 
                  /\ _pc[self] = "waitPUB2"
                  /\ (cp = any \/ cp = self)
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "PUBREC")
                                    /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBREL", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                       LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                       /\ network' = __network
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                              \/ /\ ~((packet.type = "PUBREC"))
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
waitPUBCOMP2(self) == 
                      /\ _pc[self] = "waitPUBCOMP2"
                      /\ (cp = any \/ cp = self)
                      /\ \/ /\ (Len(network[self]) > 0)
                               /\ LET pkt == Head(network[self]) IN
                                  \/ /\ (pkt.type = "PUBCOMP")
                                        /\ LET _newhead == Head(_stack[self]) IN
                                           LET __newhead == [_newhead EXCEPT !.PUBSUCC = TRUE ] IN
                                           LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                           LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                           LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (Head(___stack[self]).PUBSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                           \/ /\ ~((Head(___stack[self]).PUBSUCC = TRUE))
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                  \/ /\ ~((pkt.type = "PUBCOMP"))
                                        /\ \/ /\ (Head(_stack[self]).PUBSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                           \/ /\ ~((Head(_stack[self]).PUBSUCC = TRUE))
                                                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                                                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
l1(self) == 
            /\ _pc[self] = "l1"
            /\ (cp = any \/ cp = self)
            /\ \/ /\ (Head(_stack[self]).pkt.QoS = 0)
                     /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_11"]
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                        \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 1)
                     /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                              /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBACK", sender |-> self, topic |-> Head(_stack[self]).pkt.topic, QoS |-> 1]) IN
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_12"]
                                 /\ network' = _network
                                 /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                        \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 2)
                     /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                              /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREC", sender |-> self, topic |-> Head(_stack[self]).pkt.topic, QoS |-> 2]) IN
                                 LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \cup {Head(_stack[self]).pkt.sender})] IN
                                 /\ network' = _network
                                 /\ _Broker_data' = __Broker_data
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                        \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_11(self) == 
                /\ _pc[self] = "Lbl_11"
                /\ (cp = any \/ cp = self)
                /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                         THEN /\ LET newHead7 == Head(_stack[self]) IN
                                 LET _newHead7 == [newHead7 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                 LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                 LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead7>>) ] IN
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_11"]
                                 /\ _stack' = ___stack
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                         ELSE
                              /\ IF Head(_stack[self]).idS_sub # {}
                                       THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                               LET newHead8 == Head(_stack[self]) IN
                                               LET _newHead8 == [newHead8 EXCEPT !.sub = sub ] IN
                                               LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                               LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead8>>) ] IN
                                               LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, topic |-> Head(___stack[self]).pkt.topic, QoS |-> 0, retain |-> 1, payload |-> "bonjour", responsetopic |-> "A", correlationdata |-> "bonjour"]) IN
                                               LET __newhead == Head(___stack[self]) IN
                                               LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                               LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                               LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                               /\ IF Head(_____stack[self]).idS_sub # {}
                                                     THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_11"]
                                                             /\ _stack' = _____stack
                                                             /\ network' = _network
                                                             /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                     ELSE
                                                             /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                             /\ _stack' = _____stack
                                                             /\ network' = _network
                                                             /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                       ELSE
                                               /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                               /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_12(self) == 
                /\ _pc[self] = "Lbl_12"
                /\ (cp = any \/ cp = self)
                /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                         THEN /\ LET newHead9 == Head(_stack[self]) IN
                                 LET _newHead9 == [newHead9 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                 LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                 LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead9>>) ] IN
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_12"]
                                 /\ _stack' = ___stack
                                 /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                         ELSE
                              /\ IF Head(_stack[self]).idS_sub # {}
                                       THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                               LET newHead10 == Head(_stack[self]) IN
                                               LET _newHead10 == [newHead10 EXCEPT !.sub = sub ] IN
                                               LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                               LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead10>>) ] IN
                                               LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, topic |-> Head(___stack[self]).pkt.topic, QoS |-> 1, retain |-> 0, payload |-> "bonjour", responsetopic |-> "A", correlationdata |-> "bonjour"]) IN
                                               LET __newhead == Head(___stack[self]) IN
                                               LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                               LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                               LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                               /\ IF Head(_____stack[self]).idS_sub # {}
                                                     THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_12"]
                                                             /\ _stack' = _____stack
                                                             /\ network' = _network
                                                             /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                     ELSE
                                                             /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                             /\ _stack' = _____stack
                                                             /\ network' = _network
                                                             /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                       ELSE
                                               /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                               /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
listen(self) == 
                /\ _pc[self] = "listen"
                /\ cp = any
                /\ \/ /\ (Len(network[self]) > 0)
                         /\ LET packet == Head(network[self]) IN
                            \/ /\ (packet.type = "CONNECT")
                                  /\ \/ /\ (packet.session = 1)
                                           /\ LET _sessionClients == (sessionClients \cup {packet.sender}) IN
                                              LET _activeClients == (activeClients \cup {packet.sender}) IN
                                              LET _network == send(packet.sender, [type |-> "CONNACK", sender |-> self]) IN
                                              LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_13"]>>)] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                              /\ sessionClients' = _sessionClients
                                              /\ activeClients' = _activeClients
                                              /\ network' = _network
                                              /\ _stack' = __stack
                                              /\ UNCHANGED << depth, cp, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                     \/ /\ ~((packet.session = 1))
                                           /\ LET _activeClients == (activeClients \cup {packet.sender}) IN
                                              LET _network == send(packet.sender, [type |-> "CONNACK", sender |-> self]) IN
                                              LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_14"]>>)] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                              /\ activeClients' = _activeClients
                                              /\ network' = _network
                                              /\ _stack' = __stack
                                              /\ UNCHANGED << depth, cp, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                            \/ /\ (packet.type = "SUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \cup {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "SUBACK", sender |-> self]) IN
                                              LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_15"]>>)] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_8"]
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = _network
                                              /\ _stack' = __stack
                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                            \/ /\ (packet.type = "PUBLISH")
                                  /\ \/ /\ (packet.retain = 1)
                                           /\ LET _RetainedMessages == (RetainedMessages \cup {packet.topic}) IN
                                              \/ /\ (packet.responsetopic # packet.topic)
                                                    /\ LET _network == send(idtopic, [type |-> "PUBLISH", sender |-> self, topic |-> packet.responsetopic, QoS |-> packet.QoS, retain |-> packet.retain, payload |-> packet.correlationdata, responsetopic |-> packet.responsetopic, correlationdata |-> packet.correlationdata]) IN
                                                       LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_16"]>>)] IN
                                                       /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                                       /\ RetainedMessages' = _RetainedMessages
                                                       /\ network' = _network
                                                       /\ _stack' = __stack
                                                       /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                              \/ /\ ~((packet.responsetopic # packet.topic))
                                                    /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_17"]>>)] IN
                                                       /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                                       /\ RetainedMessages' = _RetainedMessages
                                                       /\ _stack' = __stack
                                                       /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                     \/ /\ ~((packet.retain = 1))
                                           /\ \/ /\ (packet.responsetopic # packet.topic)
                                                    /\ LET _network == send(idtopic, [type |-> "PUBLISH", sender |-> self, topic |-> packet.responsetopic, QoS |-> packet.QoS, retain |-> packet.retain, payload |-> packet.correlationdata, responsetopic |-> packet.responsetopic, correlationdata |-> packet.correlationdata]) IN
                                                       LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_18"]>>)] IN
                                                       /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                                       /\ network' = _network
                                                       /\ _stack' = __stack
                                                       /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                              \/ /\ ~((packet.responsetopic # packet.topic))
                                                    /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_19"]>>)] IN
                                                       /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                                       /\ _stack' = __stack
                                                       /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                            \/ /\ (packet.type = "PUBACK")
                                  /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                            \/ /\ (packet.type = "PUBREC")
                                  /\ LET _network == send(packet.sender, [type |-> "PUBREL", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                     LET __Broker_data == [_Broker_data EXCEPT ![self].wait_COMP = (_Broker_data[self].wait_COMP \cup {packet.sender})] IN
                                     LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                     /\ network' = __network
                                     /\ _Broker_data' = __Broker_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                            \/ /\ (packet.type = "PUBCOMP")
                                  /\ \/ /\ (({packet.sender} \cap _Broker_data[self].wait_COMP) # {})
                                           /\ LET __Broker_data == [_Broker_data EXCEPT ![self].wait_COMP = (_Broker_data[self].wait_COMP \ {packet.sender})] IN
                                              LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ _Broker_data' = __Broker_data
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap _Broker_data[self].wait_COMP) # {}))
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                            \/ /\ (packet.type = "PUBREL")
                                  /\ \/ /\ (({packet.sender} \cap _Broker_data[self].wait_REL) # {})
                                           /\ LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \ {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "PUBCOMP", sender |-> self, topic |-> packet.topic, QoS |-> 2]) IN
                                              LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_20"]>>)] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                              /\ _Broker_data' = __Broker_data
                                              /\ network' = _network
                                              /\ _stack' = __stack
                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Publisher_data, _Subscriber_data, _attaque_data >>
                                     \/ /\ ~((({packet.sender} \cap _Broker_data[self].wait_REL) # {}))
                                           /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"Lbl_21"]>>)] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                              /\ _stack' = __stack
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                            \/ /\ (packet.type = "UNSUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \ {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "UNSUBACK", sender |-> self]) IN
                                              LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = __network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                            \/ /\ (packet.type = "PINGREQ")
                                  /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, _pc |->"Lbl_22"]>>)] IN
                                     /\ _pc' = [_pc EXCEPT ![self] = "Lbl_10"]
                                     /\ _stack' = __stack
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                            \/ /\ (packet.type = "DISCONNECT")
                                  /\ LET _activeClients == (activeClients \ {packet.sender}) IN
                                     LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ activeClients' = _activeClients
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                   \/ /\ ~((Len(network[self]) > 0))
                            /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_13(self) == 
                /\ _pc[self] = "Lbl_13"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_14(self) == 
                /\ _pc[self] = "Lbl_14"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_15(self) == 
                /\ _pc[self] = "Lbl_15"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_16(self) == 
                /\ _pc[self] = "Lbl_16"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_17(self) == 
                /\ _pc[self] = "Lbl_17"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_18(self) == 
                /\ _pc[self] = "Lbl_18"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_19(self) == 
                /\ _pc[self] = "Lbl_19"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_20(self) == 
                /\ _pc[self] = "Lbl_20"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_21(self) == 
                /\ _pc[self] = "Lbl_21"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_22(self) == 
                /\ _pc[self] = "Lbl_22"
                /\ cp = any
                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                   /\ network' = _network
                   /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
_Broker(self) == 
                     listen(self) \/ Lbl_13(self) \/ Lbl_14(self) \/ Lbl_15(self) \/ Lbl_16(self) \/ Lbl_17(self) \/ Lbl_18(self) \/ Lbl_19(self) \/ Lbl_20(self) \/ Lbl_21(self) \/ Lbl_22(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self) \/ Lbl_5(self) \/ Lbl_6(self) \/ Lbl_7(self) \/ Lbl_8(self) \/ Lbl_9(self) \/ Lbl_10(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ l1(self) \/ Lbl_11(self) \/ Lbl_12(self)  
PubStart(self) == 
                  /\ _pc[self] = "PubStart"
                  /\ cp = any
                  /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "CONNECT", sender |-> self, willflag |-> 1, willqos |-> 0, willretain |-> 1, session |-> 0, keepalive |-> 60, willpayload |-> "bonjour", willtopic |-> "A"]) IN
                     /\ network' = _network
                     /\ _pc' = [_pc EXCEPT ![self] = "waitCONN"]
                     /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
waitCONN(self) == 
                  /\ _pc[self] = "waitCONN"
                  /\ cp = any
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "CONNACK")
                                    /\ LET __Publisher_data == [_Publisher_data EXCEPT ![self].CONNSUCC = TRUE] IN
                                       LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (__Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUBLISH"]
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Subscriber_data, _attaque_data, _stack >>
                                       \/ /\ ~((__Publisher_data[self].CONNSUCC = TRUE))
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Subscriber_data, _attaque_data, _stack >>
                              \/ /\ ~((packet.type = "CONNACK"))
                                    /\ \/ /\ (_Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUBLISH"]
                                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                       \/ /\ ~((_Publisher_data[self].CONNSUCC = TRUE))
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
tryPUBLISH(self) == 
                    /\ _pc[self] = "tryPUBLISH"
                    /\ cp = any
                    /\ \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "lbl"]
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                       \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                       \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB2"]
                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
lbl(self) == 
             /\ _pc[self] = "lbl"
             /\ cp = any
             /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 0, retain |-> 0, payload |-> "bonjour", responsetopic |-> "A", correlationdata |-> "bonjour"]) IN
                LET __network == send(_Publisher_data[self].BrokerID, [type |-> "PINGREQ", sender |-> self]) IN
                LET ___network == send(_Publisher_data[self].BrokerID, [type |-> "DISCONNECT", sender |-> self]) IN
                /\ network' = ___network
                /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
tryPUB1(self) == 
                 /\ _pc[self] = "tryPUB1"
                 /\ cp = any
                 /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 1, retain |-> 0, payload |-> "bonjour", responsetopic |-> "A", correlationdata |-> "bonjour"]) IN
                    /\ network' = _network
                    /\ _pc' = [_pc EXCEPT ![self] = "waitPUB1"]
                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
waitPUB1(self) == 
                  /\ _pc[self] = "waitPUB1"
                  /\ cp = any
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "PUBACK")
                                    /\ LET __Publisher_data == [_Publisher_data EXCEPT ![self].PUBSUCC = TRUE] IN
                                       LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (__Publisher_data[self].PUBSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_23"]
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Subscriber_data, _attaque_data, _stack >>
                                       \/ /\ ~((__Publisher_data[self].PUBSUCC = TRUE))
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Subscriber_data, _attaque_data, _stack >>
                              \/ /\ ~((packet.type = "PUBACK"))
                                    /\ \/ /\ (_Publisher_data[self].PUBSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_23"]
                                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                       \/ /\ ~((_Publisher_data[self].PUBSUCC = TRUE))
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                                /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_23(self) == 
                /\ _pc[self] = "Lbl_23"
                /\ cp = any
                /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "PINGREQ", sender |-> self]) IN
                   LET __network == send(_Publisher_data[self].BrokerID, [type |-> "DISCONNECT", sender |-> self]) IN
                   /\ network' = __network
                   /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
tryPUB2(self) == 
                 /\ _pc[self] = "tryPUB2"
                 /\ cp = any
                 /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[to|->_Publisher_data[self].BrokerID, PUBSUCC|->FALSE, _pc |->"Lbl_23"]>>)] IN
                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                    /\ _stack' = __stack
                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
_Publisher(self) == 
                        PubStart(self) \/ waitCONN(self) \/ tryPUBLISH(self) \/ lbl(self) \/ tryPUB1(self) \/ waitPUB1(self) \/ Lbl_23(self) \/ tryPUB2(self) \/ Lbl_23(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self) \/ Lbl_5(self) \/ Lbl_6(self) \/ Lbl_7(self) \/ Lbl_8(self) \/ Lbl_9(self) \/ Lbl_10(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self)  
Sub_start(self) == 
                   /\ _pc[self] = "Sub_start"
                   /\ cp = any
                   /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "CONNECT", sender |-> self, willflag |-> 1, willqos |-> 0, willretain |-> 1, session |-> 1, keepalive |-> 60, willpayload |-> "bonjour", willtopic |-> "A"]) IN
                      /\ network' = _network
                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitCONN"]
                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Sub_waitCONN(self) == 
                      /\ _pc[self] = "Sub_waitCONN"
                      /\ cp = any
                      /\ \/ /\ (Len(network[self]) > 0)
                               /\ LET packet == Head(network[self]) IN
                                  \/ /\ (packet.type = "CONNACK")
                                        /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].CONNSUCC = TRUE] IN
                                           LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (__Subscriber_data[self].CONNSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                    /\ _Subscriber_data' = __Subscriber_data
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                           \/ /\ ~((__Subscriber_data[self].CONNSUCC = TRUE))
                                                    /\ _Subscriber_data' = __Subscriber_data
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_start"]
                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                  \/ /\ ~((packet.type = "CONNACK"))
                                        /\ \/ /\ (_Subscriber_data[self].CONNSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                           \/ /\ ~((_Subscriber_data[self].CONNSUCC = TRUE))
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_start"]
                                                    /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Sub_subscription(self) == 
                          /\ _pc[self] = "Sub_subscription"
                          /\ cp = any
                          /\ \/ /\ TRUE
                                      /\ _pc' = [_pc EXCEPT ![self] = "sub0"]
                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                             \/ /\ TRUE
                                      /\ _pc' = [_pc EXCEPT ![self] = "sub1"]
                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                             \/ /\ TRUE
                                      /\ _pc' = [_pc EXCEPT ![self] = "sub2"]
                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
sub0(self) == 
              /\ _pc[self] = "sub0"
              /\ cp = any
              /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "SUBSCRIBE", sender |-> self, topic |-> "A", QoS |-> 0]) IN
                 /\ network' = _network
                 /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                 /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
sub1(self) == 
              /\ _pc[self] = "sub1"
              /\ cp = any
              /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "SUBSCRIBE", sender |-> self, topic |-> "A", QoS |-> 1]) IN
                 /\ network' = _network
                 /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                 /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
sub2(self) == 
              /\ _pc[self] = "sub2"
              /\ cp = any
              /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "SUBSCRIBE", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                 /\ network' = _network
                 /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                 /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Sub_waitsubscription(self) == 
                              /\ _pc[self] = "Sub_waitsubscription"
                              /\ cp = any
                              /\ \/ /\ (Len(network[self]) > 0)
                                       /\ LET packet == Head(network[self]) IN
                                          \/ /\ (packet.type = "SUBACK")
                                                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].SUBSUCC = TRUE] IN
                                                   LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                                   \/ /\ (__Subscriber_data[self].SUBSUCC = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                            /\ _Subscriber_data' = __Subscriber_data
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                   \/ /\ ~((__Subscriber_data[self].SUBSUCC = TRUE))
                                                            /\ _Subscriber_data' = __Subscriber_data
                                                            /\ network' = _network
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                                                            /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                          \/ /\ ~((packet.type = "SUBACK"))
                                                /\ \/ /\ (_Subscriber_data[self].SUBSUCC = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                                   \/ /\ ~((_Subscriber_data[self].SUBSUCC = TRUE))
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Sub_listen(self) == 
                    /\ _pc[self] = "Sub_listen"
                    /\ cp = any
                    /\ \/ /\ (Len(network[self]) > 0)
                             /\ LET packet == Head(network[self]) IN
                                \/ /\ (packet.type = "PUBLISH")
                                      /\ \/ /\ (packet.QoS = 0)
                                               /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                                                  LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                                  \/ /\ (packet.QoS = 1)
                                                        /\ LET __network == send(packet.sender, [type |-> "PUBACK", sender |-> self, topic |-> "A", QoS |-> 1]) IN
                                                           LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                                                           LET ___network == [__network EXCEPT ![self] = Tail(__network[self])] IN
                                                           \/ /\ (packet.QoS = 2)
                                                                 /\ LET ____network == send(packet.sender, [type |-> "PUBREC", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                                                    LET _____network == [____network EXCEPT ![self] = Tail(____network[self])] IN
                                                                    LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, PUBRECE|->FALSE, _pc |->"Lbl_24"]>>)] IN
                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                    /\ _Subscriber_data' = ___Subscriber_data
                                                                    /\ network' = _____network
                                                                    /\ _stack' = __stack
                                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data >>
                                                           \/ /\ ~((packet.QoS = 2))
                                                                 /\ \/ /\ (pk = TRUE)
                                                                          /\ LET ____Subscriber_data == [___Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                                                                             \/ /\ (____Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ _Subscriber_data' = ____Subscriber_data
                                                                                      /\ network' = ___network
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((____Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _Subscriber_data' = ____Subscriber_data
                                                                                      /\ network' = ___network
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                    \/ /\ ~((pk = TRUE))
                                                                          /\ \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ network' = ___network
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ network' = ___network
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                  \/ /\ ~((packet.QoS = 1))
                                                        /\ \/ /\ (packet.QoS = 2)
                                                                 /\ LET __network == send(packet.sender, [type |-> "PUBREC", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                                                    LET ___network == [__network EXCEPT ![self] = Tail(__network[self])] IN
                                                                    LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, PUBRECE|->FALSE, _pc |->"Lbl_25"]>>)] IN
                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                    /\ _Subscriber_data' = __Subscriber_data
                                                                    /\ network' = ___network
                                                                    /\ _stack' = __stack
                                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data >>
                                                           \/ /\ ~((packet.QoS = 2))
                                                                 /\ \/ /\ (pk = TRUE)
                                                                          /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                                                                             \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ network' = _network
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ network' = _network
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                    \/ /\ ~((pk = TRUE))
                                                                          /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ network' = _network
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ network' = _network
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                         \/ /\ ~((packet.QoS = 0))
                                               /\ \/ /\ (packet.QoS = 1)
                                                        /\ LET _network == send(packet.sender, [type |-> "PUBACK", sender |-> self, topic |-> "A", QoS |-> 1]) IN
                                                           LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                                                           LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                                           \/ /\ (packet.QoS = 2)
                                                                 /\ LET ___network == send(packet.sender, [type |-> "PUBREC", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                                                    LET ____network == [___network EXCEPT ![self] = Tail(___network[self])] IN
                                                                    LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, PUBRECE|->FALSE, _pc |->"Lbl_26"]>>)] IN
                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                    /\ network' = ____network
                                                                    /\ _Subscriber_data' = __Subscriber_data
                                                                    /\ _stack' = __stack
                                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data >>
                                                           \/ /\ ~((packet.QoS = 2))
                                                                 /\ \/ /\ (pk = TRUE)
                                                                          /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                                                                             \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ network' = __network
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ network' = __network
                                                                                      /\ _Subscriber_data' = ___Subscriber_data
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                    \/ /\ ~((pk = TRUE))
                                                                          /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ network' = __network
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ network' = __network
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                  \/ /\ ~((packet.QoS = 1))
                                                        /\ \/ /\ (packet.QoS = 2)
                                                                 /\ LET _network == send(packet.sender, [type |-> "PUBREC", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                                                    LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                                                    LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, PUBRECE|->FALSE, _pc |->"Lbl_27"]>>)] IN
                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                    /\ network' = __network
                                                                    /\ _stack' = __stack
                                                                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data >>
                                                           \/ /\ ~((packet.QoS = 2))
                                                                 /\ \/ /\ (pk = TRUE)
                                                                          /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                                                                             \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _Subscriber_data' = __Subscriber_data
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                                    \/ /\ ~((pk = TRUE))
                                                                          /\ \/ /\ (_Subscriber_data[self].PUBRECE = TRUE)
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                                                             \/ /\ ~((_Subscriber_data[self].PUBRECE = TRUE))
                                                                                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                                                      /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                \/ /\ ~((packet.type = "PUBLISH"))
                                      /\ \/ /\ (_Subscriber_data[self].PUBRECE = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                                  /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                         \/ /\ ~((_Subscriber_data[self].PUBRECE = TRUE))
                                                  /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                  /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Lbl_24(self) == 
                /\ _pc[self] = "Lbl_24"
                /\ cp = any
                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                   \/ /\ (pk = TRUE)
                         /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                            \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                   \/ /\ ~((pk = TRUE))
                         /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
Lbl_25(self) == 
                /\ _pc[self] = "Lbl_25"
                /\ cp = any
                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                   \/ /\ (pk = TRUE)
                         /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                            \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                   \/ /\ ~((pk = TRUE))
                         /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
Lbl_26(self) == 
                /\ _pc[self] = "Lbl_26"
                /\ cp = any
                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                   \/ /\ (pk = TRUE)
                         /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                            \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                   \/ /\ ~((pk = TRUE))
                         /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
Lbl_27(self) == 
                /\ _pc[self] = "Lbl_27"
                /\ cp = any
                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                   \/ /\ (pk = TRUE)
                         /\ LET ___Subscriber_data == [__Subscriber_data EXCEPT ![self].INJ2 = TRUE] IN
                            \/ /\ (___Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((___Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = ___Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                   \/ /\ ~((pk = TRUE))
                         /\ \/ /\ (__Subscriber_data[self].PUBRECE = TRUE)
                                     /\ _pc' = [_pc EXCEPT ![self] = "unSub_subscription"]
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                            \/ /\ ~((__Subscriber_data[self].PUBRECE = TRUE))
                                     /\ _Subscriber_data' = __Subscriber_data
                                     /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                     /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
unSub_subscription(self) == 
                            /\ _pc[self] = "unSub_subscription"
                            /\ cp = any
                            /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "UNSUBSCRIBE", topic |-> "A", sender |-> self]) IN
                               /\ network' = _network
                               /\ _pc' = [_pc EXCEPT ![self] = "unSub_waitsubscription"]
                               /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
unSub_waitsubscription(self) == 
                                /\ _pc[self] = "unSub_waitsubscription"
                                /\ cp = any
                                /\ \/ /\ (Len(network[self]) > 0)
                                         /\ LET packet == Head(network[self]) IN
                                            \/ /\ (packet.type = "UNSUBACK")
                                                  /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].UNSUBSUCC = TRUE] IN
                                                     LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                                     \/ /\ (__Subscriber_data[self].UNSUBSUCC = TRUE)
                                                              /\ _Subscriber_data' = __Subscriber_data
                                                              /\ network' = _network
                                                              /\ _pc' = [_pc EXCEPT ![self] = "pingreq"]
                                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                                     \/ /\ ~((__Subscriber_data[self].UNSUBSUCC = TRUE))
                                                              /\ _Subscriber_data' = __Subscriber_data
                                                              /\ network' = _network
                                                              /\ _pc' = [_pc EXCEPT ![self] = "pingreq"]
                                                              /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _attaque_data, _stack >>
                                            \/ /\ ~((packet.type = "UNSUBACK"))
                                                  /\ \/ /\ (_Subscriber_data[self].UNSUBSUCC = TRUE)
                                                              /\ _pc' = [_pc EXCEPT ![self] = "pingreq"]
                                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                                     \/ /\ ~((_Subscriber_data[self].UNSUBSUCC = TRUE))
                                                              /\ _pc' = [_pc EXCEPT ![self] = "pingreq"]
                                                              /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
pingreq(self) == 
                 /\ _pc[self] = "pingreq"
                 /\ cp = any
                 /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "PINGREQ", sender |-> self]) IN
                    /\ network' = _network
                    /\ _pc' = [_pc EXCEPT ![self] = "Disconnectsub"]
                    /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
Disconnectsub(self) == 
                       /\ _pc[self] = "Disconnectsub"
                       /\ cp = any
                       /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "DISCONNECT", sender |-> self]) IN
                          /\ network' = _network
                          /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
_Subscriber(self) == 
                         Sub_start(self) \/ Sub_waitCONN(self) \/ Sub_subscription(self) \/ sub0(self) \/ sub1(self) \/ sub2(self) \/ Sub_waitsubscription(self) \/ Sub_listen(self) \/ Lbl_24(self) \/ Lbl_25(self) \/ Lbl_26(self) \/ Lbl_27(self) \/ unSub_subscription(self) \/ unSub_waitsubscription(self) \/ pingreq(self) \/ Disconnectsub(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self) \/ Lbl_5(self) \/ Lbl_6(self) \/ Lbl_7(self) \/ Lbl_8(self) \/ Lbl_9(self) \/ Lbl_10(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self)  
sessionconn(self) == 
                     /\ _pc[self] = "sessionconn"
                     /\ cp = any
                     /\ \/ /\ (Len(network[_attaque_data[self].BrokerID]) > 0)
                              /\ LET packet == Head(network[_attaque_data[self].BrokerID]) IN
                                 \/ /\ (packet.type = "CONNECT")
                                       /\ \/ /\ (packet.session = 1)
                                                /\ LET __attaque_data == [_attaque_data EXCEPT ![self].OBS1 = TRUE] IN
                                                   LET ___attaque_data == [__attaque_data EXCEPT ![self].pk = packet.sender] IN
                                                   \/ /\ (___attaque_data[self].OBS1 = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                            /\ _attaque_data' = ___attaque_data
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                                   \/ /\ ~((___attaque_data[self].OBS1 = TRUE))
                                                            /\ _attaque_data' = ___attaque_data
                                                            /\ _pc' = [_pc EXCEPT ![self] = "sessionconn"]
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                          \/ /\ ~((packet.session = 1))
                                                /\ \/ /\ (_attaque_data[self].OBS1 = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                                   \/ /\ ~((_attaque_data[self].OBS1 = TRUE))
                                                            /\ _pc' = [_pc EXCEPT ![self] = "sessionconn"]
                                                            /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                 \/ /\ ~((packet.type = "CONNECT"))
                                       /\ \/ /\ (_attaque_data[self].OBS1 = TRUE)
                                                   /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                   /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                          \/ /\ ~((_attaque_data[self].OBS1 = TRUE))
                                                   /\ _pc' = [_pc EXCEPT ![self] = "sessionconn"]
                                                   /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
sessiondis(self) == 
                    /\ _pc[self] = "sessiondis"
                    /\ cp = any
                    /\ \/ /\ (Len(network[_attaque_data[self].BrokerID]) > 0)
                             /\ LET packet1 == Head(network[_attaque_data[self].BrokerID]) IN
                                \/ /\ (packet1.type = "DISCONNECT")
                                      /\ \/ /\ (_attaque_data[self].pk = packet1.sender)
                                               /\ LET __attaque_data == [_attaque_data EXCEPT ![self].OBS2 = TRUE] IN
                                                  \/ /\ (__attaque_data[self].OBS2 = TRUE)
                                                           /\ _pc' = [_pc EXCEPT ![self] = "inj"]
                                                           /\ _attaque_data' = __attaque_data
                                                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                                  \/ /\ ~((__attaque_data[self].OBS2 = TRUE))
                                                           /\ _attaque_data' = __attaque_data
                                                           /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                         \/ /\ ~((_attaque_data[self].pk = packet1.sender))
                                               /\ \/ /\ (_attaque_data[self].OBS2 = TRUE)
                                                           /\ _pc' = [_pc EXCEPT ![self] = "inj"]
                                                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                                  \/ /\ ~((_attaque_data[self].OBS2 = TRUE))
                                                           /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                           /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                \/ /\ ~((packet1.type = "DISCONNECT"))
                                      /\ \/ /\ (_attaque_data[self].OBS2 = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = "inj"]
                                                  /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
                                         \/ /\ ~((_attaque_data[self].OBS2 = TRUE))
                                                  /\ _pc' = [_pc EXCEPT ![self] = "sessiondis"]
                                                  /\ UNCHANGED << depth, cp, network, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _attaque_data, _stack >>
inj(self) == 
             /\ _pc[self] = "inj"
             /\ cp = any
             /\ LET _network == send(_attaque_data[self].BrokerID, [type |-> "CONNECT", sender |-> _attaque_data[self].pk, willflag |-> 1, willqos |-> 0, willretain |-> 1, session |-> 1, keepalive |-> 60, willpayload |-> "bonjour", willtopic |-> "A"]) IN
                LET __attaque_data == [_attaque_data EXCEPT ![self].INJ = TRUE] IN
                /\ network' = _network
                /\ _attaque_data' = __attaque_data
                /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << depth, cp, activeClients, sessionClients, idtopic, RetainedMessages, pk, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
_attaque(self) == 
                      sessionconn(self) \/ sessiondis(self) \/ inj(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self) \/ Lbl_5(self) \/ Lbl_6(self) \/ Lbl_7(self) \/ Lbl_8(self) \/ Lbl_9(self) \/ Lbl_10(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self)  

Next == (\E self \in Broker : _Broker(self))
                      \/ (\E self \in Publisher : _Publisher(self))
                      \/ (\E self \in Subscriber : _Subscriber(self))
                      \/ (\E self \in attaque : _attaque(self))
                      \/ ((\A self \in ProcSet : _pc[self] = "Done")
                          /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Temp0 == (~ \A I \in attaque : (((_attaque_data[I].OBS1 = TRUE) /\ (<> (_attaque_data[I].OBS2 = TRUE))) => (<> (_attaque_data[I].INJ = TRUE))))

=================================================================================
