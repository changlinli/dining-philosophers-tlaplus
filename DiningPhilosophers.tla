------------------------- MODULE DiningPhilosophers -------------------------

EXTENDS FiniteSets, Integers

CONSTANTS NumOfPhilosophers

ASSUME NumOfPhilosophers \in Nat

ASSUME NumOfPhilosophers >= 2

VARIABLES philosopherStates, philosopherToForks

vars == <<philosopherStates, philosopherToForks>>

Philosophers == 1..NumOfPhilosophers

Forks == 1..NumOfPhilosophers

NextFork(fork) == ((fork + 1) % NumOfPhilosophers) + 1

PhilosophersHoldingFork(fork) == { p \in Philosophers : fork \in philosopherToForks[p] }

Range(f) == { f[x] : x \in DOMAIN f }

ForkIsAvailable(fork) == fork \notin UNION Range(philosopherToForks)

TypeOK ==
    /\ Cardinality(Forks) = NumOfPhilosophers
    /\ philosopherStates \in [Philosophers -> {"thinking", "waitingForFirstFork", "waitingForSecondFork", "eating", "setDownFirstFork"}]
    /\ \A p \in Philosophers :
        \/ philosopherToForks[p] = {}
        \/ philosopherToForks[p] = {p}
        \/ philosopherToForks[p] = {NextFork(p)}
        \/ philosopherToForks[p] = {p, NextFork(p)}
    /\ \A f \in Forks : Cardinality(PhilosophersHoldingFork(f)) <= 1
    /\ \A f \in Forks : ForkIsAvailable(f) => PhilosophersHoldingFork(f) = {}
    /\ \A p \in Philosophers :
        /\ philosopherStates[p] = "thinking" => philosopherToForks[p] = {}
        /\ philosopherStates[p] = "waitingForFirstFork" => philosopherToForks[p] = {}
        /\ philosopherStates[p] = "waitingForSecondFork" => Cardinality(philosopherToForks[p]) = 1
        /\ philosopherStates[p] = "eating" => Cardinality(philosopherToForks[p]) = 2
        /\ philosopherStates[p] = "setDownFirstFork" => Cardinality(philosopherToForks[p]) = 1

Init ==
    /\ philosopherStates = [p \in Philosophers |-> "thinking"]
    /\ philosopherToForks = [f \in Philosophers |-> {}]

WaitForFork == \E p \in Philosophers :
    /\ philosopherStates[p] = "thinking"
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForFirstFork"]
    /\ UNCHANGED philosopherToForks
        
PickUpFirstFork == \E p \in Philosophers :
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\
        \/ IF ForkIsAvailable(p) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = {p}] ELSE
            FALSE
        \/ IF ForkIsAvailable(NextFork(p)) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = {NextFork(p)}] ELSE
            FALSE
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]
        
PickUpSecondFork == \E p \in Philosophers :
    /\ philosopherStates[p] = "waitingForSecondFork"
    /\
        \/ IF ForkIsAvailable(p) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {p}] ELSE
            FALSE
        \/ IF ForkIsAvailable(NextFork(p)) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {NextFork(p)}] ELSE
            FALSE
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "eating"]

SetDownFirstFork == \E p \in Philosophers :
    /\ philosopherStates[p] = "eating"
    /\ \E f \in philosopherToForks[p] : 
        philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \ {f}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "setDownFirstFork"]

SetDownSecondFork == \E p \in Philosophers :
    /\ philosopherStates[p] = "setDownFirstFork"
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "thinking"]
    
Next ==
    \/ WaitForFork
    \/ PickUpFirstFork
    \/ PickUpSecondFork
    \/ SetDownFirstFork
    \/ SetDownSecondFork
    
Spec == Init /\ [][Next]_vars

=============================================================================