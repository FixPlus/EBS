-------------------------------- MODULE EBS --------------------------------


EXTENDS Integers, Sequences, TLC

CONSTANT Senders
CONSTANT Recievers
CONSTANT LocNum
CONSTANT MsgsToSend

(*
/* Elimination backoff stack algorithm.
/* https://people.csail.mit.edu/shanir/publications/Lock_Free.pdf 
--fair algorithm EBS{

variables main_stack = << 0 >>,
          \* Use tag here to solve ABA problem
          StackTop = [val |-> 0, tag |-> 0],
          collision = [n \in 1..LocNum |->[val |-> <<>>, tag |-> 0]],
          locations = [p \in Senders \union Recievers  |->  [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> 0]],
          MsgsToSendCounter = MsgsToSend,
          MsgsRecievedCounter = 0,
          RcvdMsgs = {};
define {
\* Correctness 
  AllWasRecieved == <>(\A n \in 1..MsgsToSend : n \in RcvdMsgs)
  NoOtherMsgsRecieved == [](\A n \in RcvdMsgs : n \in 1..MsgsToSend)
};

macro CAS(success, ptr, old, new) {
    if (ptr = old) {
        ptr := new;
        success := TRUE;
    }
    else
        success := FALSE;
}

macro FinishCollision(){
  if(info.op = "pop"){
    info.msg := locations[self].val.msg;
    locations[self] := [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> locations[self].tag + 1]
  }
}

procedure lesOp()
variables pos, myloc, q, him, LocSet = 1..LocNum, c_cas_ok = FALSE;
{
  trial_loop: while(TRUE) {
     load_collison:
     locations[self] := [ val |-> info, tag |-> locations[self].tag + 1];
     myloc := locations[self];
     pos := RandomElement(LocSet);
     c_cas_ok := FALSE;
     him := collision[pos];
     c_cas_once: 
     CAS(c_cas_ok, collision[pos], him, [val |-> <<self>>, tag |-> him.tag + 1]);
     c_cas_loop: 
     while(c_cas_ok = FALSE){
       him := collision[pos];
       cas_try: CAS(c_cas_ok, collision[pos], him, [ val |-> <<self>>, tag |-> him.tag + 1])
     };
     
     check_collision:
     if(Len(him.val) /= 0){
       q := locations[Head(him.val)];
       \* Push/Pop collision
       if(Len(q.val.id) /= 0 /\ Head(q.val.id) = Head(him.val) /\ q.val.op /= info.op){
         l_cas_once:
         CAS(c_cas_ok, locations[self], myloc, [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> myloc.tag + 1]);
         if(c_cas_ok){
           \* Try collision
           try_collison1:
           if(info.op = "push"){
             tc_cas_once1:
             CAS(c_cas_ok, locations[Head(him.val)], q, [val |-> info, tag |-> q.tag + 1]);
           } else if(info.op = "pop"){
             \* locations[anotherId] -> NULL
             tc_cas_once2:
             CAS(c_cas_ok, locations[Head(him.val)], q, [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> q.tag + 1]);
             tc_check_cas:
             if(c_cas_ok){
               info.msg := q.val.msg;
               \* locations[self] -> NULL
               locations[self] := [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> locations[self].tag + 1];
             }
           };
           check_collision_cas:
           if(c_cas_ok)
             return;
           else
             goto fin_stack;
         } else {
            fin_collison1:
            FinishCollision();
            post_finish1:
            return;
         }
       }
       
     };
     
     \* delay(spin)
     c_cas_once1:
     CAS(c_cas_ok, locations[self], myloc, [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> myloc.tag + 1]);
     if(c_cas_ok = FALSE){
       fin_collison2:
       FinishCollision();
       post_finish2:
       return;
     };
     fin_stack:
     call tryPerformOnStack();
     fin_stack_check:
     if(try_check){
       return;
     }
  };
}

procedure tryPerformOnStack()
variables head, top, cas_check
{
  do_push: if(info.op = "push"){
    read_head1:
    
    head := Head(main_stack);
    top := StackTop;
    
    cas_once1:
    CAS(cas_check, StackTop, top, [val |-> StackTop.val + 1, tag |-> StackTop.tag + 1]);
    if(cas_check){
      main_stack := <<info.msg>> \o main_stack;
      try_check := TRUE;
    } else {
      try_check := FALSE;
    };
    finish_push: return
  };
  
  do_pop: if(info.op = "pop"){
    read_head2:
    
    head := Head(main_stack);
    top := StackTop;
    
    check_empty:
    if(top.val = 0){
      info.msg := -1;
      try_check := FALSE;
      early_exit_ion_empty: return
    };
     
    cas_once2:
    CAS(cas_check, StackTop, top, [val |-> StackTop.val - 1, tag |-> StackTop.tag + 1]);
    if(cas_check){
      main_stack := Tail(main_stack);
      info.msg := head;
      try_check := TRUE;
    } else{
      info.msg := -1;
      try_check := FALSE;
    };
    finish_pop: return
  };
}
procedure stackOp(info)
variables try_check
{
  try_main_stack: call tryPerformOnStack();
  check_failed: if(try_check = FALSE){
    call lesOp();
  };
  copy_back: if(info.op = "pop"){
    RcvInfo := info;
  };
  finish: return
}

process (s \in Senders)
variables SendInfo = [id |-> <<self>>, op |-> "push", msg |-> -1], msg_cas_check = FALSE;
{
  
  push_loop: while(MsgsToSendCounter > 0){
     get_message: SendInfo.msg := MsgsToSendCounter;
     MsgsToSendCounter := MsgsToSendCounter - 1;
     check_msg: if(SendInfo.msg > 0){
       perform_push: call stackOp(SendInfo)
     }
  }
}

process (r \in Recievers)
variable RcvInfo = [id |-> <<self>>, op |-> "pop", msg |-> -1];
{
  pop_loop: while(MsgsRecievedCounter < MsgsToSend){
     await Len(main_stack) > 1;
     perform_pop: call stackOp(RcvInfo);
     \* Increment only if popped successfully
     increment_rcv: if(RcvInfo.msg /= -1){
       MsgsRecievedCounter := MsgsRecievedCounter + 1;
       assert(~(RcvInfo.msg \in RcvdMsgs));
       RcvdMsgs := RcvdMsgs \union {RcvInfo.msg};
     }
  }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b065c69e" /\ chksum(tla) = "85931afb")
CONSTANT defaultInitValue
VARIABLES main_stack, StackTop, collision, locations, MsgsToSendCounter, 
          MsgsRecievedCounter, RcvdMsgs, pc, stack

(* define statement *)
AllWasRecieved == <>(\A n \in 1..MsgsToSend : n \in RcvdMsgs)
NoOtherMsgsRecieved == [](\A n \in RcvdMsgs : n \in 1..MsgsToSend)

VARIABLES pos, myloc, q, him, LocSet, c_cas_ok, head, top, cas_check, info, 
          try_check, SendInfo, msg_cas_check, RcvInfo

vars == << main_stack, StackTop, collision, locations, MsgsToSendCounter, 
           MsgsRecievedCounter, RcvdMsgs, pc, stack, pos, myloc, q, him, 
           LocSet, c_cas_ok, head, top, cas_check, info, try_check, SendInfo, 
           msg_cas_check, RcvInfo >>

ProcSet == (Senders) \cup (Recievers)

Init == (* Global variables *)
        /\ main_stack = << 0 >>
        /\ StackTop = [val |-> 0, tag |-> 0]
        /\ collision = [n \in 1..LocNum |->[val |-> <<>>, tag |-> 0]]
        /\ locations = [p \in Senders \union Recievers  |->  [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> 0]]
        /\ MsgsToSendCounter = MsgsToSend
        /\ MsgsRecievedCounter = 0
        /\ RcvdMsgs = {}
        (* Procedure lesOp *)
        /\ pos = [ self \in ProcSet |-> defaultInitValue]
        /\ myloc = [ self \in ProcSet |-> defaultInitValue]
        /\ q = [ self \in ProcSet |-> defaultInitValue]
        /\ him = [ self \in ProcSet |-> defaultInitValue]
        /\ LocSet = [ self \in ProcSet |-> 1..LocNum]
        /\ c_cas_ok = [ self \in ProcSet |-> FALSE]
        (* Procedure tryPerformOnStack *)
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        /\ top = [ self \in ProcSet |-> defaultInitValue]
        /\ cas_check = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure stackOp *)
        /\ info = [ self \in ProcSet |-> defaultInitValue]
        /\ try_check = [ self \in ProcSet |-> defaultInitValue]
        (* Process s *)
        /\ SendInfo = [self \in Senders |-> [id |-> <<self>>, op |-> "push", msg |-> -1]]
        /\ msg_cas_check = [self \in Senders |-> FALSE]
        (* Process r *)
        /\ RcvInfo = [self \in Recievers |-> [id |-> <<self>>, op |-> "pop", msg |-> -1]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Senders -> "push_loop"
                                        [] self \in Recievers -> "pop_loop"]

trial_loop(self) == /\ pc[self] = "trial_loop"
                    /\ pc' = [pc EXCEPT ![self] = "load_collison"]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, him, 
                                    LocSet, c_cas_ok, head, top, cas_check, 
                                    info, try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

load_collison(self) == /\ pc[self] = "load_collison"
                       /\ locations' = [locations EXCEPT ![self] = [ val |-> info[self], tag |-> locations[self].tag + 1]]
                       /\ myloc' = [myloc EXCEPT ![self] = locations'[self]]
                       /\ pos' = [pos EXCEPT ![self] = RandomElement(LocSet[self])]
                       /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                       /\ him' = [him EXCEPT ![self] = collision[pos'[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "c_cas_once"]
                       /\ UNCHANGED << main_stack, StackTop, collision, 
                                       MsgsToSendCounter, MsgsRecievedCounter, 
                                       RcvdMsgs, stack, q, LocSet, head, top, 
                                       cas_check, info, try_check, SendInfo, 
                                       msg_cas_check, RcvInfo >>

c_cas_once(self) == /\ pc[self] = "c_cas_once"
                    /\ IF (collision[pos[self]]) = him[self]
                          THEN /\ collision' = [collision EXCEPT ![pos[self]] = [val |-> <<self>>, tag |-> him[self].tag + 1]]
                               /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                          ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                               /\ UNCHANGED collision
                    /\ pc' = [pc EXCEPT ![self] = "c_cas_loop"]
                    /\ UNCHANGED << main_stack, StackTop, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, him, 
                                    LocSet, head, top, cas_check, info, 
                                    try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

c_cas_loop(self) == /\ pc[self] = "c_cas_loop"
                    /\ IF c_cas_ok[self] = FALSE
                          THEN /\ him' = [him EXCEPT ![self] = collision[pos[self]]]
                               /\ pc' = [pc EXCEPT ![self] = "cas_try"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "check_collision"]
                               /\ him' = him
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, LocSet, 
                                    c_cas_ok, head, top, cas_check, info, 
                                    try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

cas_try(self) == /\ pc[self] = "cas_try"
                 /\ IF (collision[pos[self]]) = him[self]
                       THEN /\ collision' = [collision EXCEPT ![pos[self]] = [ val |-> <<self>>, tag |-> him[self].tag + 1]]
                            /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                       ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                            /\ UNCHANGED collision
                 /\ pc' = [pc EXCEPT ![self] = "c_cas_loop"]
                 /\ UNCHANGED << main_stack, StackTop, locations, 
                                 MsgsToSendCounter, MsgsRecievedCounter, 
                                 RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                 head, top, cas_check, info, try_check, 
                                 SendInfo, msg_cas_check, RcvInfo >>

check_collision(self) == /\ pc[self] = "check_collision"
                         /\ IF Len(him[self].val) /= 0
                               THEN /\ q' = [q EXCEPT ![self] = locations[Head(him[self].val)]]
                                    /\ IF Len(q'[self].val.id) /= 0 /\ Head(q'[self].val.id) = Head(him[self].val) /\ q'[self].val.op /= info[self].op
                                          THEN /\ pc' = [pc EXCEPT ![self] = "l_cas_once"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "c_cas_once1"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "c_cas_once1"]
                                    /\ q' = q
                         /\ UNCHANGED << main_stack, StackTop, collision, 
                                         locations, MsgsToSendCounter, 
                                         MsgsRecievedCounter, RcvdMsgs, stack, 
                                         pos, myloc, him, LocSet, c_cas_ok, 
                                         head, top, cas_check, info, try_check, 
                                         SendInfo, msg_cas_check, RcvInfo >>

l_cas_once(self) == /\ pc[self] = "l_cas_once"
                    /\ IF (locations[self]) = myloc[self]
                          THEN /\ locations' = [locations EXCEPT ![self] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> myloc[self].tag + 1]]
                               /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                          ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                               /\ UNCHANGED locations
                    /\ IF c_cas_ok'[self]
                          THEN /\ pc' = [pc EXCEPT ![self] = "try_collison1"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "fin_collison1"]
                    /\ UNCHANGED << main_stack, StackTop, collision, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, him, 
                                    LocSet, head, top, cas_check, info, 
                                    try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

try_collison1(self) == /\ pc[self] = "try_collison1"
                       /\ IF info[self].op = "push"
                             THEN /\ pc' = [pc EXCEPT ![self] = "tc_cas_once1"]
                             ELSE /\ IF info[self].op = "pop"
                                        THEN /\ pc' = [pc EXCEPT ![self] = "tc_cas_once2"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "check_collision_cas"]
                       /\ UNCHANGED << main_stack, StackTop, collision, 
                                       locations, MsgsToSendCounter, 
                                       MsgsRecievedCounter, RcvdMsgs, stack, 
                                       pos, myloc, q, him, LocSet, c_cas_ok, 
                                       head, top, cas_check, info, try_check, 
                                       SendInfo, msg_cas_check, RcvInfo >>

tc_cas_once1(self) == /\ pc[self] = "tc_cas_once1"
                      /\ IF (locations[Head(him[self].val)]) = q[self]
                            THEN /\ locations' = [locations EXCEPT ![Head(him[self].val)] = [val |-> info[self], tag |-> q[self].tag + 1]]
                                 /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                            ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                                 /\ UNCHANGED locations
                      /\ pc' = [pc EXCEPT ![self] = "check_collision_cas"]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      MsgsToSendCounter, MsgsRecievedCounter, 
                                      RcvdMsgs, stack, pos, myloc, q, him, 
                                      LocSet, head, top, cas_check, info, 
                                      try_check, SendInfo, msg_cas_check, 
                                      RcvInfo >>

tc_cas_once2(self) == /\ pc[self] = "tc_cas_once2"
                      /\ IF (locations[Head(him[self].val)]) = q[self]
                            THEN /\ locations' = [locations EXCEPT ![Head(him[self].val)] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> q[self].tag + 1]]
                                 /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                            ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                                 /\ UNCHANGED locations
                      /\ pc' = [pc EXCEPT ![self] = "tc_check_cas"]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      MsgsToSendCounter, MsgsRecievedCounter, 
                                      RcvdMsgs, stack, pos, myloc, q, him, 
                                      LocSet, head, top, cas_check, info, 
                                      try_check, SendInfo, msg_cas_check, 
                                      RcvInfo >>

tc_check_cas(self) == /\ pc[self] = "tc_check_cas"
                      /\ IF c_cas_ok[self]
                            THEN /\ info' = [info EXCEPT ![self].msg = q[self].val.msg]
                                 /\ locations' = [locations EXCEPT ![self] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> locations[self].tag + 1]]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << locations, info >>
                      /\ pc' = [pc EXCEPT ![self] = "check_collision_cas"]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      MsgsToSendCounter, MsgsRecievedCounter, 
                                      RcvdMsgs, stack, pos, myloc, q, him, 
                                      LocSet, c_cas_ok, head, top, cas_check, 
                                      try_check, SendInfo, msg_cas_check, 
                                      RcvInfo >>

check_collision_cas(self) == /\ pc[self] = "check_collision_cas"
                             /\ IF c_cas_ok[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ pos' = [pos EXCEPT ![self] = Head(stack[self]).pos]
                                        /\ myloc' = [myloc EXCEPT ![self] = Head(stack[self]).myloc]
                                        /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
                                        /\ him' = [him EXCEPT ![self] = Head(stack[self]).him]
                                        /\ LocSet' = [LocSet EXCEPT ![self] = Head(stack[self]).LocSet]
                                        /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = Head(stack[self]).c_cas_ok]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "fin_stack"]
                                        /\ UNCHANGED << stack, pos, myloc, q, 
                                                        him, LocSet, c_cas_ok >>
                             /\ UNCHANGED << main_stack, StackTop, collision, 
                                             locations, MsgsToSendCounter, 
                                             MsgsRecievedCounter, RcvdMsgs, 
                                             head, top, cas_check, info, 
                                             try_check, SendInfo, 
                                             msg_cas_check, RcvInfo >>

fin_collison1(self) == /\ pc[self] = "fin_collison1"
                       /\ IF info[self].op = "pop"
                             THEN /\ info' = [info EXCEPT ![self].msg = locations[self].val.msg]
                                  /\ locations' = [locations EXCEPT ![self] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> locations[self].tag + 1]]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << locations, info >>
                       /\ pc' = [pc EXCEPT ![self] = "post_finish1"]
                       /\ UNCHANGED << main_stack, StackTop, collision, 
                                       MsgsToSendCounter, MsgsRecievedCounter, 
                                       RcvdMsgs, stack, pos, myloc, q, him, 
                                       LocSet, c_cas_ok, head, top, cas_check, 
                                       try_check, SendInfo, msg_cas_check, 
                                       RcvInfo >>

post_finish1(self) == /\ pc[self] = "post_finish1"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ pos' = [pos EXCEPT ![self] = Head(stack[self]).pos]
                      /\ myloc' = [myloc EXCEPT ![self] = Head(stack[self]).myloc]
                      /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
                      /\ him' = [him EXCEPT ![self] = Head(stack[self]).him]
                      /\ LocSet' = [LocSet EXCEPT ![self] = Head(stack[self]).LocSet]
                      /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = Head(stack[self]).c_cas_ok]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      locations, MsgsToSendCounter, 
                                      MsgsRecievedCounter, RcvdMsgs, head, top, 
                                      cas_check, info, try_check, SendInfo, 
                                      msg_cas_check, RcvInfo >>

c_cas_once1(self) == /\ pc[self] = "c_cas_once1"
                     /\ IF (locations[self]) = myloc[self]
                           THEN /\ locations' = [locations EXCEPT ![self] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> myloc[self].tag + 1]]
                                /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = TRUE]
                           ELSE /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                                /\ UNCHANGED locations
                     /\ IF c_cas_ok'[self] = FALSE
                           THEN /\ pc' = [pc EXCEPT ![self] = "fin_collison2"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "fin_stack"]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     MsgsToSendCounter, MsgsRecievedCounter, 
                                     RcvdMsgs, stack, pos, myloc, q, him, 
                                     LocSet, head, top, cas_check, info, 
                                     try_check, SendInfo, msg_cas_check, 
                                     RcvInfo >>

fin_collison2(self) == /\ pc[self] = "fin_collison2"
                       /\ IF info[self].op = "pop"
                             THEN /\ info' = [info EXCEPT ![self].msg = locations[self].val.msg]
                                  /\ locations' = [locations EXCEPT ![self] = [val |-> [id |-> <<>>, op |-> "pop", msg |-> -1], tag |-> locations[self].tag + 1]]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << locations, info >>
                       /\ pc' = [pc EXCEPT ![self] = "post_finish2"]
                       /\ UNCHANGED << main_stack, StackTop, collision, 
                                       MsgsToSendCounter, MsgsRecievedCounter, 
                                       RcvdMsgs, stack, pos, myloc, q, him, 
                                       LocSet, c_cas_ok, head, top, cas_check, 
                                       try_check, SendInfo, msg_cas_check, 
                                       RcvInfo >>

post_finish2(self) == /\ pc[self] = "post_finish2"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ pos' = [pos EXCEPT ![self] = Head(stack[self]).pos]
                      /\ myloc' = [myloc EXCEPT ![self] = Head(stack[self]).myloc]
                      /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
                      /\ him' = [him EXCEPT ![self] = Head(stack[self]).him]
                      /\ LocSet' = [LocSet EXCEPT ![self] = Head(stack[self]).LocSet]
                      /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = Head(stack[self]).c_cas_ok]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      locations, MsgsToSendCounter, 
                                      MsgsRecievedCounter, RcvdMsgs, head, top, 
                                      cas_check, info, try_check, SendInfo, 
                                      msg_cas_check, RcvInfo >>

fin_stack(self) == /\ pc[self] = "fin_stack"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tryPerformOnStack",
                                                            pc        |->  "fin_stack_check",
                                                            head      |->  head[self],
                                                            top       |->  top[self],
                                                            cas_check |->  cas_check[self] ] >>
                                                        \o stack[self]]
                   /\ head' = [head EXCEPT ![self] = defaultInitValue]
                   /\ top' = [top EXCEPT ![self] = defaultInitValue]
                   /\ cas_check' = [cas_check EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "do_push"]
                   /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                   MsgsToSendCounter, MsgsRecievedCounter, 
                                   RcvdMsgs, pos, myloc, q, him, LocSet, 
                                   c_cas_ok, info, try_check, SendInfo, 
                                   msg_cas_check, RcvInfo >>

fin_stack_check(self) == /\ pc[self] = "fin_stack_check"
                         /\ IF try_check[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ pos' = [pos EXCEPT ![self] = Head(stack[self]).pos]
                                    /\ myloc' = [myloc EXCEPT ![self] = Head(stack[self]).myloc]
                                    /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
                                    /\ him' = [him EXCEPT ![self] = Head(stack[self]).him]
                                    /\ LocSet' = [LocSet EXCEPT ![self] = Head(stack[self]).LocSet]
                                    /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = Head(stack[self]).c_cas_ok]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "trial_loop"]
                                    /\ UNCHANGED << stack, pos, myloc, q, him, 
                                                    LocSet, c_cas_ok >>
                         /\ UNCHANGED << main_stack, StackTop, collision, 
                                         locations, MsgsToSendCounter, 
                                         MsgsRecievedCounter, RcvdMsgs, head, 
                                         top, cas_check, info, try_check, 
                                         SendInfo, msg_cas_check, RcvInfo >>

lesOp(self) == trial_loop(self) \/ load_collison(self) \/ c_cas_once(self)
                  \/ c_cas_loop(self) \/ cas_try(self)
                  \/ check_collision(self) \/ l_cas_once(self)
                  \/ try_collison1(self) \/ tc_cas_once1(self)
                  \/ tc_cas_once2(self) \/ tc_check_cas(self)
                  \/ check_collision_cas(self) \/ fin_collison1(self)
                  \/ post_finish1(self) \/ c_cas_once1(self)
                  \/ fin_collison2(self) \/ post_finish2(self)
                  \/ fin_stack(self) \/ fin_stack_check(self)

do_push(self) == /\ pc[self] = "do_push"
                 /\ IF info[self].op = "push"
                       THEN /\ pc' = [pc EXCEPT ![self] = "read_head1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "do_pop"]
                 /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                 MsgsToSendCounter, MsgsRecievedCounter, 
                                 RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                 c_cas_ok, head, top, cas_check, info, 
                                 try_check, SendInfo, msg_cas_check, RcvInfo >>

read_head1(self) == /\ pc[self] = "read_head1"
                    /\ head' = [head EXCEPT ![self] = Head(main_stack)]
                    /\ top' = [top EXCEPT ![self] = StackTop]
                    /\ pc' = [pc EXCEPT ![self] = "cas_once1"]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, him, 
                                    LocSet, c_cas_ok, cas_check, info, 
                                    try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

cas_once1(self) == /\ pc[self] = "cas_once1"
                   /\ IF StackTop = top[self]
                         THEN /\ StackTop' = [val |-> StackTop.val + 1, tag |-> StackTop.tag + 1]
                              /\ cas_check' = [cas_check EXCEPT ![self] = TRUE]
                         ELSE /\ cas_check' = [cas_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED StackTop
                   /\ IF cas_check'[self]
                         THEN /\ main_stack' = <<info[self].msg>> \o main_stack
                              /\ try_check' = [try_check EXCEPT ![self] = TRUE]
                         ELSE /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED main_stack
                   /\ pc' = [pc EXCEPT ![self] = "finish_push"]
                   /\ UNCHANGED << collision, locations, MsgsToSendCounter, 
                                   MsgsRecievedCounter, RcvdMsgs, stack, pos, 
                                   myloc, q, him, LocSet, c_cas_ok, head, top, 
                                   info, SendInfo, msg_cas_check, RcvInfo >>

finish_push(self) == /\ pc[self] = "finish_push"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                     /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                     /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, RcvdMsgs, pos, myloc, 
                                     q, him, LocSet, c_cas_ok, info, try_check, 
                                     SendInfo, msg_cas_check, RcvInfo >>

do_pop(self) == /\ pc[self] = "do_pop"
                /\ IF info[self].op = "pop"
                      THEN /\ pc' = [pc EXCEPT ![self] = "read_head2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                MsgsToSendCounter, MsgsRecievedCounter, 
                                RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                c_cas_ok, head, top, cas_check, info, 
                                try_check, SendInfo, msg_cas_check, RcvInfo >>

read_head2(self) == /\ pc[self] = "read_head2"
                    /\ head' = [head EXCEPT ![self] = Head(main_stack)]
                    /\ top' = [top EXCEPT ![self] = StackTop]
                    /\ pc' = [pc EXCEPT ![self] = "check_empty"]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, stack, pos, myloc, q, him, 
                                    LocSet, c_cas_ok, cas_check, info, 
                                    try_check, SendInfo, msg_cas_check, 
                                    RcvInfo >>

check_empty(self) == /\ pc[self] = "check_empty"
                     /\ IF top[self].val = 0
                           THEN /\ info' = [info EXCEPT ![self].msg = -1]
                                /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "early_exit_ion_empty"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "cas_once2"]
                                /\ UNCHANGED << info, try_check >>
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, RcvdMsgs, stack, pos, 
                                     myloc, q, him, LocSet, c_cas_ok, head, 
                                     top, cas_check, SendInfo, msg_cas_check, 
                                     RcvInfo >>

early_exit_ion_empty(self) == /\ pc[self] = "early_exit_ion_empty"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                              /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                              /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << main_stack, StackTop, collision, 
                                              locations, MsgsToSendCounter, 
                                              MsgsRecievedCounter, RcvdMsgs, 
                                              pos, myloc, q, him, LocSet, 
                                              c_cas_ok, info, try_check, 
                                              SendInfo, msg_cas_check, RcvInfo >>

cas_once2(self) == /\ pc[self] = "cas_once2"
                   /\ IF StackTop = top[self]
                         THEN /\ StackTop' = [val |-> StackTop.val - 1, tag |-> StackTop.tag + 1]
                              /\ cas_check' = [cas_check EXCEPT ![self] = TRUE]
                         ELSE /\ cas_check' = [cas_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED StackTop
                   /\ IF cas_check'[self]
                         THEN /\ main_stack' = Tail(main_stack)
                              /\ info' = [info EXCEPT ![self].msg = head[self]]
                              /\ try_check' = [try_check EXCEPT ![self] = TRUE]
                         ELSE /\ info' = [info EXCEPT ![self].msg = -1]
                              /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED main_stack
                   /\ pc' = [pc EXCEPT ![self] = "finish_pop"]
                   /\ UNCHANGED << collision, locations, MsgsToSendCounter, 
                                   MsgsRecievedCounter, RcvdMsgs, stack, pos, 
                                   myloc, q, him, LocSet, c_cas_ok, head, top, 
                                   SendInfo, msg_cas_check, RcvInfo >>

finish_pop(self) == /\ pc[self] = "finish_pop"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                    /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                    /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    RcvdMsgs, pos, myloc, q, him, LocSet, 
                                    c_cas_ok, info, try_check, SendInfo, 
                                    msg_cas_check, RcvInfo >>

tryPerformOnStack(self) == do_push(self) \/ read_head1(self)
                              \/ cas_once1(self) \/ finish_push(self)
                              \/ do_pop(self) \/ read_head2(self)
                              \/ check_empty(self)
                              \/ early_exit_ion_empty(self)
                              \/ cas_once2(self) \/ finish_pop(self)

try_main_stack(self) == /\ pc[self] = "try_main_stack"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tryPerformOnStack",
                                                                 pc        |->  "check_failed",
                                                                 head      |->  head[self],
                                                                 top       |->  top[self],
                                                                 cas_check |->  cas_check[self] ] >>
                                                             \o stack[self]]
                        /\ head' = [head EXCEPT ![self] = defaultInitValue]
                        /\ top' = [top EXCEPT ![self] = defaultInitValue]
                        /\ cas_check' = [cas_check EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "do_push"]
                        /\ UNCHANGED << main_stack, StackTop, collision, 
                                        locations, MsgsToSendCounter, 
                                        MsgsRecievedCounter, RcvdMsgs, pos, 
                                        myloc, q, him, LocSet, c_cas_ok, info, 
                                        try_check, SendInfo, msg_cas_check, 
                                        RcvInfo >>

check_failed(self) == /\ pc[self] = "check_failed"
                      /\ IF try_check[self] = FALSE
                            THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lesOp",
                                                                          pc        |->  "copy_back",
                                                                          pos       |->  pos[self],
                                                                          myloc     |->  myloc[self],
                                                                          q         |->  q[self],
                                                                          him       |->  him[self],
                                                                          LocSet    |->  LocSet[self],
                                                                          c_cas_ok  |->  c_cas_ok[self] ] >>
                                                                      \o stack[self]]
                                 /\ pos' = [pos EXCEPT ![self] = defaultInitValue]
                                 /\ myloc' = [myloc EXCEPT ![self] = defaultInitValue]
                                 /\ q' = [q EXCEPT ![self] = defaultInitValue]
                                 /\ him' = [him EXCEPT ![self] = defaultInitValue]
                                 /\ LocSet' = [LocSet EXCEPT ![self] = 1..LocNum]
                                 /\ c_cas_ok' = [c_cas_ok EXCEPT ![self] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "trial_loop"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "copy_back"]
                                 /\ UNCHANGED << stack, pos, myloc, q, him, 
                                                 LocSet, c_cas_ok >>
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      locations, MsgsToSendCounter, 
                                      MsgsRecievedCounter, RcvdMsgs, head, top, 
                                      cas_check, info, try_check, SendInfo, 
                                      msg_cas_check, RcvInfo >>

copy_back(self) == /\ pc[self] = "copy_back"
                   /\ IF info[self].op = "pop"
                         THEN /\ RcvInfo' = [RcvInfo EXCEPT ![self] = info[self]]
                         ELSE /\ TRUE
                              /\ UNCHANGED RcvInfo
                   /\ pc' = [pc EXCEPT ![self] = "finish"]
                   /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                   MsgsToSendCounter, MsgsRecievedCounter, 
                                   RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                   c_cas_ok, head, top, cas_check, info, 
                                   try_check, SendInfo, msg_cas_check >>

finish(self) == /\ pc[self] = "finish"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ try_check' = [try_check EXCEPT ![self] = Head(stack[self]).try_check]
                /\ info' = [info EXCEPT ![self] = Head(stack[self]).info]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                MsgsToSendCounter, MsgsRecievedCounter, 
                                RcvdMsgs, pos, myloc, q, him, LocSet, c_cas_ok, 
                                head, top, cas_check, SendInfo, msg_cas_check, 
                                RcvInfo >>

stackOp(self) == try_main_stack(self) \/ check_failed(self)
                    \/ copy_back(self) \/ finish(self)

push_loop(self) == /\ pc[self] = "push_loop"
                   /\ IF MsgsToSendCounter > 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "get_message"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                   MsgsToSendCounter, MsgsRecievedCounter, 
                                   RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                   c_cas_ok, head, top, cas_check, info, 
                                   try_check, SendInfo, msg_cas_check, RcvInfo >>

get_message(self) == /\ pc[self] = "get_message"
                     /\ SendInfo' = [SendInfo EXCEPT ![self].msg = MsgsToSendCounter]
                     /\ MsgsToSendCounter' = MsgsToSendCounter - 1
                     /\ pc' = [pc EXCEPT ![self] = "check_msg"]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsRecievedCounter, RcvdMsgs, 
                                     stack, pos, myloc, q, him, LocSet, 
                                     c_cas_ok, head, top, cas_check, info, 
                                     try_check, msg_cas_check, RcvInfo >>

check_msg(self) == /\ pc[self] = "check_msg"
                   /\ IF SendInfo[self].msg > 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "perform_push"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "push_loop"]
                   /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                   MsgsToSendCounter, MsgsRecievedCounter, 
                                   RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                   c_cas_ok, head, top, cas_check, info, 
                                   try_check, SendInfo, msg_cas_check, RcvInfo >>

perform_push(self) == /\ pc[self] = "perform_push"
                      /\ /\ info' = [info EXCEPT ![self] = SendInfo[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "stackOp",
                                                                  pc        |->  "push_loop",
                                                                  try_check |->  try_check[self],
                                                                  info      |->  info[self] ] >>
                                                              \o stack[self]]
                      /\ try_check' = [try_check EXCEPT ![self] = defaultInitValue]
                      /\ pc' = [pc EXCEPT ![self] = "try_main_stack"]
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      locations, MsgsToSendCounter, 
                                      MsgsRecievedCounter, RcvdMsgs, pos, 
                                      myloc, q, him, LocSet, c_cas_ok, head, 
                                      top, cas_check, SendInfo, msg_cas_check, 
                                      RcvInfo >>

s(self) == push_loop(self) \/ get_message(self) \/ check_msg(self)
              \/ perform_push(self)

pop_loop(self) == /\ pc[self] = "pop_loop"
                  /\ IF MsgsRecievedCounter < MsgsToSend
                        THEN /\ Len(main_stack) > 1
                             /\ pc' = [pc EXCEPT ![self] = "perform_pop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                  MsgsToSendCounter, MsgsRecievedCounter, 
                                  RcvdMsgs, stack, pos, myloc, q, him, LocSet, 
                                  c_cas_ok, head, top, cas_check, info, 
                                  try_check, SendInfo, msg_cas_check, RcvInfo >>

perform_pop(self) == /\ pc[self] = "perform_pop"
                     /\ /\ info' = [info EXCEPT ![self] = RcvInfo[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "stackOp",
                                                                 pc        |->  "increment_rcv",
                                                                 try_check |->  try_check[self],
                                                                 info      |->  info[self] ] >>
                                                             \o stack[self]]
                     /\ try_check' = [try_check EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "try_main_stack"]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, RcvdMsgs, pos, myloc, 
                                     q, him, LocSet, c_cas_ok, head, top, 
                                     cas_check, SendInfo, msg_cas_check, 
                                     RcvInfo >>

increment_rcv(self) == /\ pc[self] = "increment_rcv"
                       /\ IF RcvInfo[self].msg /= -1
                             THEN /\ MsgsRecievedCounter' = MsgsRecievedCounter + 1
                                  /\ Assert((~(RcvInfo[self].msg \in RcvdMsgs)), 
                                            "Failure of assertion at line 202, column 8.")
                                  /\ RcvdMsgs' = (RcvdMsgs \union {RcvInfo[self].msg})
                             ELSE /\ TRUE
                                  /\ UNCHANGED << MsgsRecievedCounter, 
                                                  RcvdMsgs >>
                       /\ pc' = [pc EXCEPT ![self] = "pop_loop"]
                       /\ UNCHANGED << main_stack, StackTop, collision, 
                                       locations, MsgsToSendCounter, stack, 
                                       pos, myloc, q, him, LocSet, c_cas_ok, 
                                       head, top, cas_check, info, try_check, 
                                       SendInfo, msg_cas_check, RcvInfo >>

r(self) == pop_loop(self) \/ perform_pop(self) \/ increment_rcv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ lesOp(self) \/ tryPerformOnStack(self)
                               \/ stackOp(self))
           \/ (\E self \in Senders: s(self))
           \/ (\E self \in Recievers: r(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed May 24 13:11:54 MSK 2023 by dybv-sc
\* Last modified Sun May 14 05:57:15 MSK 2023 by ����� �������
\* Created Sun May 14 00:33:34 MSK 2023 by ����� �������
