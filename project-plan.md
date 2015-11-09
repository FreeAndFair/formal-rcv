Project Plan
========

The following is a rough-cut strawman proposal for what we might want to do
in terms of formalizing ranked-choice and instant runoff voting schemes.
I'm not very knowledgable about elections, so those of you with more knowledge
in this area, feel free to modify as appropriate...

Step 0 - Specification and implementation
-------------------

Select a small number of variants (2 or 3) to specify and implement.
This involves, for each variant:

- writing down the specification, ideally with reference to the relevant statutes
- demonstrating that the specification uniquely determines the outcome of an election
- give a specific algorithm implementing the specification and show that it terminates

Step 1 - Functional Correctness and voting theory
-------------------------

Identify some functional correctness properties to demonstrate.  For example:

- Prove the Condorcet property for systems that have it
- Prove the later-no-harm property for systems that have it

Step 2 - Tactical Voting
--------------------

Develop enough game theory to tackle questions about voting tactics.

- Resistance to specific tactical voting techiques...

Step 2 - Risk Limiting auditing
------------------------

Joey has mentioned doing some work regarding auditing.  I'm not very familiar
with this, but I think it has something to do with robustness of the auditing
procedure under some adversarial activity.
