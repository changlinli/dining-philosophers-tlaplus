------------------------- MODULE DiningPhilosophers -------------------------

EXTENDS FiniteSets, Integers

CONSTANTS NumOfPhilosophers

NumOfPhilosophersIsNaturalNumber == NumOfPhilosophers \in Nat

ASSUME NumOfPhilosophersIsNaturalNumber

ThereIsMoreThanOnePhilosopher == NumOfPhilosophers >= 2

ASSUME ThereIsMoreThanOnePhilosopher

VARIABLES philosopherStates, philosopherToForks

vars == <<philosopherStates, philosopherToForks>>

Philosophers == 1..NumOfPhilosophers

Forks == 1..NumOfPhilosophers

NextFork(fork) == IF fork < NumOfPhilosophers THEN fork + 1 ELSE ((fork + 1) % NumOfPhilosophers) + 1

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

WaitForFork(p) ==
    /\ philosopherStates[p] = "thinking"
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForFirstFork"]
    /\ UNCHANGED philosopherToForks
        
PickUpFirstFork(p) ==
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\
        \/
            /\ ForkIsAvailable(p)
            /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {p}]
        \/
            /\ ForkIsAvailable(NextFork(p))
            /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {NextFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]
        
PickUpSecondFork(p) ==
    /\ philosopherStates[p] = "waitingForSecondFork"
    /\
        \/
            /\ ForkIsAvailable(p)
            /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {p}]
        \/  /\ ForkIsAvailable(NextFork(p))
            /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {NextFork(p)}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "eating"]

SetDownFirstFork(p) ==
    /\ philosopherStates[p] = "eating"
    /\ \E f \in philosopherToForks[p] : 
        philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \ {f}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "setDownFirstFork"]

SetDownSecondFork(p) ==
    /\ philosopherStates[p] = "setDownFirstFork"
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "thinking"]
    
Next == \E p \in Philosophers :
    \/ WaitForFork(p)
    \/ PickUpFirstFork(p)
    \/ PickUpSecondFork(p)
    \/ SetDownFirstFork(p)
    \/ SetDownSecondFork(p)
    
Spec == Init /\ [][Next]_vars

SpecWithFairness == Spec /\ WF_vars(Next)

AllPhilosophersEventuallyEat == \A p \in Philosophers : <> (philosopherStates[p] = "eating")

=============================================================================