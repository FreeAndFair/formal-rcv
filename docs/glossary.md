Glossary
========

This document provides definitions of a number of election and RCV-related
terms for the purposes of this project.  As much as possible, the names
of functions, variables, etc. in this project will be chosen to be
consistent with these definitions.

Note that the statutes of individual jurisdictions may assign different
meanings to these terms.  For example, San Francisco Charter
[Section 13.102(a)][SF_Charter_13_102_a] takes "ballot" to mean "vote"
in the sense of this glossary.  For this reason, the project strives to
distinguish visually when a term is being used with the global project
meaning as opposed to the the meaning as assigned by the statute being
discussed.


Terms
-----

* **ballot**.  An object on which a voter can mark or save their votes
  for an election and then subsequently cast.  Frequently, a ballot is one
  or more paper cards.  For example, the City and County of San Francisco
  sometimes has a 5-card ballot.  In the case of a
  [DRE voting machine][DRE_voting_machine] without a paper trail, the ballot
  can be a data structure stored in an electronic medium.

* **contest**.

* **exhausted vote**.

* **overvote**.

* **round**.  A sequential stage of the vote tabulation for an RCV contest.

* **undervote**.

* **vote**.  The physical or electronic markings that contain a
  voter's selections cast for a single contest in an election.  For example,
  in the case of a "vote for one" contest, a vote could be a bubbled-in
  oval or, in the case of a vote for a write-in candidate, a bubbled-in
  oval in conjunction with a hand-written name.  In the case of an RCV
  contest, a vote would be the collection of markings indicating a voter's
  first, second, and third choices, etc.

* **vote record**.


[DRE_voting_machine]: https://en.wikipedia.org/wiki/DRE_voting_machine
[SF_Charter_13_102_a]: ../statutes/san_francisco.txt#L11
