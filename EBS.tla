-------------------------------- MODULE EBS --------------------------------


EXTENDS Integers, Sequences

CONSTANT Senders
CONSTANT Recievers
CONSTANT LocNum
CONSTANT MsgsToSend

(*

--fair algorithm EBS{

variables main_stack = << 0 >>,
          StackTop = 0,
          collision = [p \in Senders \union Recievers  |-> -1],
          locations = [n \in 1..LocNum |-> [id |-> -1, op |-> "pop", msg |-> -1]],
          MsgsToSendCounter = MsgsToSend,
          MsgsRecievedCounter = 0;

macro CAS(success, ptr, old, new) {
    if (ptr = old) {
        ptr := new;
        success := TRUE;
    }
    else
        success := FALSE;
}

procedure tryPerformOnStack(info)
variables head, top, cas_check
{
  do_push: if(info.op = "push"){
    read_head1:
    
    head := Head(main_stack);
    top := StackTop;
    
    cas_once1:
    CAS(cas_check, StackTop, top, StackTop + 1);
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
    if(top = 0){
      info.msg := -1;
      try_check := FALSE;
      early_exit_ion_empty: return
    };
     
    cas_once2:
    CAS(cas_check, StackTop, top, StackTop - 1);
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
procedure lesOp(info) {
  do_nothing: return
}
procedure stackOp(info)
variables try_check
{
  try_main_stack: call tryPerformOnStack(info);
  check_failed: if(try_check = FALSE){
    call lesOp(info);
  };
  finish: return
}

process (s \in Senders)
variables SendInfo = [id |-> self, op |-> "push", msg |-> -1], Succ = FALSE;
{
  push_loop: while(MsgsToSendCounter > 0){  
     get_message: SendInfo.msg := MsgsToSendCounter;
     MsgsToSendCounter := MsgsToSendCounter - 1;
     perform_push: call stackOp(SendInfo)
  }
}

process (r \in Recievers)
variables RcvInfo = [id |-> self, op |-> "pop", msg |-> -1], Succ = FALSE;
{
  pop_loop: while(MsgsRecievedCounter < MsgsToSendCounter){
     await Len(main_stack) > 1;
     perform_pop: call stackOp(RcvInfo);
     increment_msg_count:
     MsgsRecievedCounter := MsgsRecievedCounter + 1;
  }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "af907fa6" /\ chksum(tla) = "6df0fe1e")
\* Process variable Succ of process s at line 91 col 64 changed to Succ_
\* Parameter info of procedure tryPerformOnStack at line 31 col 29 changed to info_
\* Parameter info of procedure lesOp at line 77 col 17 changed to info_l
CONSTANT defaultInitValue
VARIABLES main_stack, StackTop, collision, locations, MsgsToSendCounter, 
          MsgsRecievedCounter, pc, stack, info_, head, top, cas_check, info_l, 
          info, try_check, SendInfo, Succ_, RcvInfo, Succ

vars == << main_stack, StackTop, collision, locations, MsgsToSendCounter, 
           MsgsRecievedCounter, pc, stack, info_, head, top, cas_check, 
           info_l, info, try_check, SendInfo, Succ_, RcvInfo, Succ >>

ProcSet == (Senders) \cup (Recievers)

Init == (* Global variables *)
        /\ main_stack = << 0 >>
        /\ StackTop = 0
        /\ collision = [p \in Senders \union Recievers  |-> -1]
        /\ locations = [n \in 1..LocNum |-> [id |-> -1, op |-> "pop", msg |-> -1]]
        /\ MsgsToSendCounter = MsgsToSend
        /\ MsgsRecievedCounter = 0
        (* Procedure tryPerformOnStack *)
        /\ info_ = [ self \in ProcSet |-> defaultInitValue]
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        /\ top = [ self \in ProcSet |-> defaultInitValue]
        /\ cas_check = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lesOp *)
        /\ info_l = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure stackOp *)
        /\ info = [ self \in ProcSet |-> defaultInitValue]
        /\ try_check = [ self \in ProcSet |-> defaultInitValue]
        (* Process s *)
        /\ SendInfo = [self \in Senders |-> [id |-> self, op |-> "push", msg |-> -1]]
        /\ Succ_ = [self \in Senders |-> FALSE]
        (* Process r *)
        /\ RcvInfo = [self \in Recievers |-> [id |-> self, op |-> "pop", msg |-> -1]]
        /\ Succ = [self \in Recievers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Senders -> "push_loop"
                                        [] self \in Recievers -> "pop_loop"]

do_push(self) == /\ pc[self] = "do_push"
                 /\ IF info_[self].op = "push"
                       THEN /\ pc' = [pc EXCEPT ![self] = "read_head1"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "do_pop"]
                 /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                 MsgsToSendCounter, MsgsRecievedCounter, stack, 
                                 info_, head, top, cas_check, info_l, info, 
                                 try_check, SendInfo, Succ_, RcvInfo, Succ >>

read_head1(self) == /\ pc[self] = "read_head1"
                    /\ head' = [head EXCEPT ![self] = Head(main_stack)]
                    /\ top' = [top EXCEPT ![self] = StackTop]
                    /\ pc' = [pc EXCEPT ![self] = "cas_once1"]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    stack, info_, cas_check, info_l, info, 
                                    try_check, SendInfo, Succ_, RcvInfo, Succ >>

cas_once1(self) == /\ pc[self] = "cas_once1"
                   /\ IF StackTop = top[self]
                         THEN /\ StackTop' = StackTop + 1
                              /\ cas_check' = [cas_check EXCEPT ![self] = TRUE]
                         ELSE /\ cas_check' = [cas_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED StackTop
                   /\ IF cas_check'[self]
                         THEN /\ main_stack' = <<info_[self].msg>> \o main_stack
                              /\ try_check' = [try_check EXCEPT ![self] = TRUE]
                         ELSE /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED main_stack
                   /\ pc' = [pc EXCEPT ![self] = "finish_push"]
                   /\ UNCHANGED << collision, locations, MsgsToSendCounter, 
                                   MsgsRecievedCounter, stack, info_, head, 
                                   top, info_l, info, SendInfo, Succ_, RcvInfo, 
                                   Succ >>

finish_push(self) == /\ pc[self] = "finish_push"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                     /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                     /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                     /\ info_' = [info_ EXCEPT ![self] = Head(stack[self]).info_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, info_l, info, 
                                     try_check, SendInfo, Succ_, RcvInfo, Succ >>

do_pop(self) == /\ pc[self] = "do_pop"
                /\ IF info_[self].op = "pop"
                      THEN /\ pc' = [pc EXCEPT ![self] = "read_head2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                MsgsToSendCounter, MsgsRecievedCounter, stack, 
                                info_, head, top, cas_check, info_l, info, 
                                try_check, SendInfo, Succ_, RcvInfo, Succ >>

read_head2(self) == /\ pc[self] = "read_head2"
                    /\ head' = [head EXCEPT ![self] = Head(main_stack)]
                    /\ top' = [top EXCEPT ![self] = StackTop]
                    /\ pc' = [pc EXCEPT ![self] = "check_empty"]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    stack, info_, cas_check, info_l, info, 
                                    try_check, SendInfo, Succ_, RcvInfo, Succ >>

check_empty(self) == /\ pc[self] = "check_empty"
                     /\ IF top[self] = 0
                           THEN /\ info_' = [info_ EXCEPT ![self].msg = -1]
                                /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "early_exit_ion_empty"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "cas_once2"]
                                /\ UNCHANGED << info_, try_check >>
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, stack, head, top, 
                                     cas_check, info_l, info, SendInfo, Succ_, 
                                     RcvInfo, Succ >>

early_exit_ion_empty(self) == /\ pc[self] = "early_exit_ion_empty"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                              /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                              /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                              /\ info_' = [info_ EXCEPT ![self] = Head(stack[self]).info_]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << main_stack, StackTop, collision, 
                                              locations, MsgsToSendCounter, 
                                              MsgsRecievedCounter, info_l, 
                                              info, try_check, SendInfo, Succ_, 
                                              RcvInfo, Succ >>

cas_once2(self) == /\ pc[self] = "cas_once2"
                   /\ IF StackTop = top[self]
                         THEN /\ StackTop' = StackTop - 1
                              /\ cas_check' = [cas_check EXCEPT ![self] = TRUE]
                         ELSE /\ cas_check' = [cas_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED StackTop
                   /\ IF cas_check'[self]
                         THEN /\ main_stack' = Tail(main_stack)
                              /\ info_' = [info_ EXCEPT ![self].msg = head[self]]
                              /\ try_check' = [try_check EXCEPT ![self] = TRUE]
                         ELSE /\ info_' = [info_ EXCEPT ![self].msg = -1]
                              /\ try_check' = [try_check EXCEPT ![self] = FALSE]
                              /\ UNCHANGED main_stack
                   /\ pc' = [pc EXCEPT ![self] = "finish_pop"]
                   /\ UNCHANGED << collision, locations, MsgsToSendCounter, 
                                   MsgsRecievedCounter, stack, head, top, 
                                   info_l, info, SendInfo, Succ_, RcvInfo, 
                                   Succ >>

finish_pop(self) == /\ pc[self] = "finish_pop"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                    /\ top' = [top EXCEPT ![self] = Head(stack[self]).top]
                    /\ cas_check' = [cas_check EXCEPT ![self] = Head(stack[self]).cas_check]
                    /\ info_' = [info_ EXCEPT ![self] = Head(stack[self]).info_]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    info_l, info, try_check, SendInfo, Succ_, 
                                    RcvInfo, Succ >>

tryPerformOnStack(self) == do_push(self) \/ read_head1(self)
                              \/ cas_once1(self) \/ finish_push(self)
                              \/ do_pop(self) \/ read_head2(self)
                              \/ check_empty(self)
                              \/ early_exit_ion_empty(self)
                              \/ cas_once2(self) \/ finish_pop(self)

do_nothing(self) == /\ pc[self] = "do_nothing"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ info_l' = [info_l EXCEPT ![self] = Head(stack[self]).info_l]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                    MsgsToSendCounter, MsgsRecievedCounter, 
                                    info_, head, top, cas_check, info, 
                                    try_check, SendInfo, Succ_, RcvInfo, Succ >>

lesOp(self) == do_nothing(self)

try_main_stack(self) == /\ pc[self] = "try_main_stack"
                        /\ /\ info_' = [info_ EXCEPT ![self] = info[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tryPerformOnStack",
                                                                    pc        |->  "check_failed",
                                                                    head      |->  head[self],
                                                                    top       |->  top[self],
                                                                    cas_check |->  cas_check[self],
                                                                    info_     |->  info_[self] ] >>
                                                                \o stack[self]]
                        /\ head' = [head EXCEPT ![self] = defaultInitValue]
                        /\ top' = [top EXCEPT ![self] = defaultInitValue]
                        /\ cas_check' = [cas_check EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "do_push"]
                        /\ UNCHANGED << main_stack, StackTop, collision, 
                                        locations, MsgsToSendCounter, 
                                        MsgsRecievedCounter, info_l, info, 
                                        try_check, SendInfo, Succ_, RcvInfo, 
                                        Succ >>

check_failed(self) == /\ pc[self] = "check_failed"
                      /\ IF try_check[self] = FALSE
                            THEN /\ /\ info_l' = [info_l EXCEPT ![self] = info[self]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lesOp",
                                                                             pc        |->  "finish",
                                                                             info_l    |->  info_l[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "do_nothing"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "finish"]
                                 /\ UNCHANGED << stack, info_l >>
                      /\ UNCHANGED << main_stack, StackTop, collision, 
                                      locations, MsgsToSendCounter, 
                                      MsgsRecievedCounter, info_, head, top, 
                                      cas_check, info, try_check, SendInfo, 
                                      Succ_, RcvInfo, Succ >>

finish(self) == /\ pc[self] = "finish"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ try_check' = [try_check EXCEPT ![self] = Head(stack[self]).try_check]
                /\ info' = [info EXCEPT ![self] = Head(stack[self]).info]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                MsgsToSendCounter, MsgsRecievedCounter, info_, 
                                head, top, cas_check, info_l, SendInfo, Succ_, 
                                RcvInfo, Succ >>

stackOp(self) == try_main_stack(self) \/ check_failed(self) \/ finish(self)

push_loop(self) == /\ pc[self] = "push_loop"
                   /\ IF MsgsToSendCounter > 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "get_message"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                   MsgsToSendCounter, MsgsRecievedCounter, 
                                   stack, info_, head, top, cas_check, info_l, 
                                   info, try_check, SendInfo, Succ_, RcvInfo, 
                                   Succ >>

get_message(self) == /\ pc[self] = "get_message"
                     /\ SendInfo' = [SendInfo EXCEPT ![self].msg = MsgsToSendCounter]
                     /\ MsgsToSendCounter' = MsgsToSendCounter - 1
                     /\ pc' = [pc EXCEPT ![self] = "perform_push"]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsRecievedCounter, stack, 
                                     info_, head, top, cas_check, info_l, info, 
                                     try_check, Succ_, RcvInfo, Succ >>

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
                                      MsgsRecievedCounter, info_, head, top, 
                                      cas_check, info_l, SendInfo, Succ_, 
                                      RcvInfo, Succ >>

s(self) == push_loop(self) \/ get_message(self) \/ perform_push(self)

pop_loop(self) == /\ pc[self] = "pop_loop"
                  /\ IF MsgsRecievedCounter < MsgsToSendCounter
                        THEN /\ Len(main_stack) > 1
                             /\ pc' = [pc EXCEPT ![self] = "perform_pop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << main_stack, StackTop, collision, locations, 
                                  MsgsToSendCounter, MsgsRecievedCounter, 
                                  stack, info_, head, top, cas_check, info_l, 
                                  info, try_check, SendInfo, Succ_, RcvInfo, 
                                  Succ >>

perform_pop(self) == /\ pc[self] = "perform_pop"
                     /\ /\ info' = [info EXCEPT ![self] = RcvInfo[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "stackOp",
                                                                 pc        |->  "increment_msg_count",
                                                                 try_check |->  try_check[self],
                                                                 info      |->  info[self] ] >>
                                                             \o stack[self]]
                     /\ try_check' = [try_check EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "try_main_stack"]
                     /\ UNCHANGED << main_stack, StackTop, collision, 
                                     locations, MsgsToSendCounter, 
                                     MsgsRecievedCounter, info_, head, top, 
                                     cas_check, info_l, SendInfo, Succ_, 
                                     RcvInfo, Succ >>

increment_msg_count(self) == /\ pc[self] = "increment_msg_count"
                             /\ MsgsRecievedCounter' = MsgsRecievedCounter + 1
                             /\ pc' = [pc EXCEPT ![self] = "pop_loop"]
                             /\ UNCHANGED << main_stack, StackTop, collision, 
                                             locations, MsgsToSendCounter, 
                                             stack, info_, head, top, 
                                             cas_check, info_l, info, 
                                             try_check, SendInfo, Succ_, 
                                             RcvInfo, Succ >>

r(self) == pop_loop(self) \/ perform_pop(self) \/ increment_msg_count(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ tryPerformOnStack(self) \/ lesOp(self)
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
\* Last modified Sun May 14 05:57:15 MSK 2023 by Ѕушев ƒмитрий
\* Created Sun May 14 00:33:34 MSK 2023 by Ѕушев ƒмитрий
