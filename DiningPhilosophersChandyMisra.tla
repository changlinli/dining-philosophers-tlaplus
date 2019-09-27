------------------- MODULE DiningPhilosophersChandyMisra -------------------

EXTENDS FiniteSets, Integers, Sequences

CONSTANTS NumOfPhilosophers, RightHandedPhilosopher

NumOfPhilosophersIsNaturalNumber == NumOfPhilosophers \in Nat

ASSUME NumOfPhilosophersIsNaturalNumber

ThereIsMoreThanOnePhilosopher == NumOfPhilosophers >= 2

ASSUME ThereIsMoreThanOnePhilosopher

VARIABLES philosopherStates, philosopherToForks, forkRequests, forkStates

vars == <<philosopherStates, philosopherToForks>>

DiningPhilosophers == INSTANCE DiningPhilosophers

Philosophers == 1..NumOfPhilosophers

Forks == 1..NumOfPhilosophers

NextFork(fork) == IF fork < NumOfPhilosophers THEN fork + 1 ELSE ((fork + 1) % NumOfPhilosophers) + 1

PhilosophersHoldingFork(fork) == { p \in Philosophers : fork \in philosopherToForks[p] }

Range(f) == { f[x] : x \in DOMAIN f }

ForkIsAvailable(fork) == fork \notin UNION Range(philosopherToForks)

RightFork(fork) == DiningPhilosophers!NextFork(fork)

LeftFork(fork) == fork

PickUpFirstForkLeftHandedPhilosopher(p) ==
    /\ p /= RightHandedPhilosopher
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\ IF DiningPhilosophers!ForkIsAvailable(LeftFork(p))
        THEN
            /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {LeftFork(p)}]
            /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]
        ELSE
            /\ forkRequests' = [forkRequests EXCEPT ![LeftFork(p)] = p]

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
    /\ LeftFork(p) \in forkRequests[LeftFork(p)] =>
        /\ [forkRequests EXCEPT ![LeftFork(p)] = {}]
        /\ philosopherTo

SendForkOver(p) ==    
    /\ philosopherStates[p] = "sendingFirstForkOver"
    /\
        \/ CASE 
            forkRequests[p] /= {} ->
                /\ forkStates[p] = "clean"
                /\ philosopherStates[p] = "setDownFirstFork"
                /\ \E f \in philosopherToForks[p] : 
                    philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \ {f}]
                /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "setDownFirstFork"]
            forkRequests[p] = {} ->
                /\ 

TypeOK == 
    /\ DiningPhilosophers!TypeOK
    /\ forkStates \in [Forks -> {"clean", "dirty"}]
    /\ forkRequests \in [Forks -> {{}, {p \in Philosophers : {p}}}]


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

SpecWithFairness == Spec /\ WF_vars(Next)

AllPhilosophersEventuallyEat == \A p \in Philosophers : <> (philosopherStates[p] = "eating")

=============================================================================
\* Modification History
\* Last modified Fri Aug 16 15:27:18 EDT 2019 by changlin
\* Created Tue Aug 13 20:44:57 EDT 2019 by changlin
