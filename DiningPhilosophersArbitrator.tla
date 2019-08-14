-------------------- MODULE DiningPhilosophersArbitrator --------------------

CONSTANTS NumOfPhilosophers

VARIABLES philosopherToForks, philosopherStates, arbitrator

vars == <<philosopherToForks, philosopherStates, arbitrator>>

DiningPhilosophers == INSTANCE DiningPhilosophers

ASSUME DiningPhilosophers!NumOfPhilosophersIsNaturalNumber
ASSUME DiningPhilosophers!ThereIsMoreThanOnePhilosopher

TypeOK == 
    /\ DiningPhilosophers!TypeOK
    /\ arbitrator \in {{}, { DiningPhilosophers!Philosophers }}

AskForPermission(philosopher) ==
    /\ arbitrator = {}
    /\ arbitrator' = { philosopher }
    /\ UNCHANGED <<philosopherToForks, philosopherStates>>

ArbitratedPickUpFirstFork(philosopher) ==
    /\ philosopher \in arbitrator
    /\ DiningPhilosophers!PickUpFirstFork(philosopher)
    
ArbitratedPickUpSecondFork(philosopher) ==
    /\ philosopher \in arbitrator
    /\ DiningPhilosophers!PickUpSecondFork(philosopher)
    
ReleaseArbitrator(philosopher) ==
    /\ philosopherStates[philosopher] = "thinking"
    /\ arbitrator' = arbitrator \ { philosopher }
    /\ UNCHANGED <<philosopherToForks, philosopherStates>>

Init ==
    /\ DiningPhilosophers!Init
    /\ arbitrator = {}
    
Next == \E p \in DiningPhilosophers!Philosophers :
    \/ DiningPhilosophers!WaitForFork(p) /\ UNCHANGED arbitrator
    \/ ArbitratedPickUpFirstFork(p) /\ UNCHANGED arbitrator
    \/ ArbitratedPickUpSecondFork(p) /\ UNCHANGED arbitrator
    \/ DiningPhilosophers!SetDownFirstFork(p) /\ UNCHANGED arbitrator
    \/ DiningPhilosophers!SetDownSecondFork(p) /\ UNCHANGED arbitrator
    \/ AskForPermission(p)
    \/ ReleaseArbitrator(p)
    
Spec == Init /\ [][Next]_vars

SpecWithFairness == 
    /\ Spec
    /\ WF_vars(Next)
    /\ \A p \in DiningPhilosophers!Philosophers : WF_vars(DiningPhilosophers!WaitForFork(p) /\ UNCHANGED arbitrator)
    /\ \A p \in DiningPhilosophers!Philosophers : SF_vars(ReleaseArbitrator(p))
    /\ \A p \in DiningPhilosophers!Philosophers : SF_vars(AskForPermission(p))
    
THEOREM Spec => DiningPhilosophers!Spec

THEOREM SpecWithFairness => DiningPhilosophers!AllPhilosophersEventuallyEat
=============================================================================
\* Modification History
\* Last modified Tue Aug 13 16:56:13 EDT 2019 by changlin
\* Created Mon Aug 12 18:29:48 EDT 2019 by changlin
