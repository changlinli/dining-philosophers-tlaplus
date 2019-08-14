---------------- MODULE DiningPhilosophersResourceHierarchy ----------------

EXTENDS Integers

CONSTANTS NumOfPhilosophers, RightHandedPhilosopher

ASSUME RightHandedPhilosopher < NumOfPhilosophers /\ RightHandedPhilosopher >= 0

Philosophers == 1..NumOfPhilosophers

VARIABLES philosopherStates, philosopherToForks

vars == <<philosopherStates, philosopherToForks>>

DiningPhilosophers == INSTANCE DiningPhilosophers

RightFork(fork) == DiningPhilosophers!NextFork(fork)

LeftFork(fork) == fork

PickUpFirstForkLeftHandedPhilosopher(p) ==
    /\ p /= RightHandedPhilosopher
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\ DiningPhilosophers!ForkIsAvailable(LeftFork(p))
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {LeftFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]

PickUpSecondForkLeftHandedPhilosopher(p) ==
    /\ p /= RightHandedPhilosopher
    /\ philosopherStates[p] = "waitingForSecondFork"
    /\ DiningPhilosophers!ForkIsAvailable(RightFork(p))
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {RightFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "eating"]
    
PickUpFirstForkRightHandedPhilosopher(p) ==
    /\ p = RightHandedPhilosopher
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\ DiningPhilosophers!ForkIsAvailable(RightFork(p))
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {RightFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]

PickUpSecondForkRightHandedPhilosopher(p) ==
    /\ p = RightHandedPhilosopher
    /\ philosopherStates[p] = "waitingForSecondFork"
    /\ DiningPhilosophers!ForkIsAvailable(LeftFork(p))
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {LeftFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "eating"]
    
NextPerPhilosopher(p) ==
    \/ DiningPhilosophers!WaitForFork(p)
    \/ PickUpFirstForkLeftHandedPhilosopher(p)
    \/ PickUpSecondForkLeftHandedPhilosopher(p)
    \/ PickUpFirstForkRightHandedPhilosopher(p)
    \/ PickUpSecondForkRightHandedPhilosopher(p)
    \/ DiningPhilosophers!SetDownFirstFork(p)
    \/ DiningPhilosophers!SetDownSecondFork(p)
        
Next == \E p \in Philosophers : NextPerPhilosopher(p)
    
Spec == DiningPhilosophers!Init /\ [][Next]_vars

SpecWithFairness == 
    /\ Spec
    /\ \A p \in Philosophers : SF_vars(NextPerPhilosopher(p))

THEOREM Spec => DiningPhilosophers!TypeOK

THEOREM Spec => DiningPhilosophers!AllPhilosophersEventuallyEat

=============================================================================
\* Modification History
\* Last modified Tue Aug 13 18:41:06 EDT 2019 by changlin
\* Created Tue Aug 13 16:17:21 EDT 2019 by changlin
