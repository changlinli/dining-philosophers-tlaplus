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
    /\ UNCHANGED arbitrator
    
ArbitratedPickUpSecondFork(philosopher) ==
    /\ philosopher \in arbitrator
    /\ DiningPhilosophers!PickUpSecondFork(philosopher)
    /\ UNCHANGED arbitrator
    
ReleaseArbitrator(philosopher) ==
    /\ philosopherStates[philosopher] = "thinking"
    /\ arbitrator' = arbitrator \ { philosopher }
    /\ UNCHANGED <<philosopherToForks, philosopherStates>>

Init ==
    /\ DiningPhilosophers!Init
    /\ arbitrator = {}
    
Next == \E p \in DiningPhilosophers!Philosophers :
    \/ DiningPhilosophers!WaitForFork(p) /\ UNCHANGED arbitrator
    \/ AskForPermission(p)
    \/ ArbitratedPickUpFirstFork(p)
    \/ ArbitratedPickUpSecondFork(p)
    \/ DiningPhilosophers!SetDownFirstFork(p) /\ UNCHANGED arbitrator
    \/ DiningPhilosophers!SetDownSecondFork(p) /\ UNCHANGED arbitrator
    \/ ReleaseArbitrator(p)
    
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Aug 12 19:06:43 EDT 2019 by changlin
\* Created Mon Aug 12 18:29:48 EDT 2019 by changlin
