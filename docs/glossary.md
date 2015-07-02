Glossary
========

This document provides definitions of a number of election and RCV-related
terms for the purposes of this project.  As much as possible, the names of
functions, variables, etc. in this project will be chosen to be consistent
with these definitions.

These definitions should be taken as informative rather than normative.
However, they should be consistent with and descriptive of the normative
definitions that we spell out elsewhere in the project using a formal
language.

Note that the statutes of individual jurisdictions may assign different
meanings to these terms.  For example, San Francisco Charter
[Section 13.102.a][SF_Charter_13_102_a] takes "ballot" to mean "vote"
in the sense of this glossary.  For this reason, the project strives to
distinguish visually when a term is being used with the global project
meaning as opposed to the meaning as assigned by the statute being
discussed.


Terms
-----

* **ballot**.  An object on which a voter can mark or save all of their
  selections for an election and then subsequently cast.  Frequently, a
  ballot is one or more paper cards.  For example, the City and County of
  San Francisco sometimes has a 5-card ballot.  In the case of a
  [DRE voting machine][DRE_voting_machine] without a paper trail, the ballot
  can be a data structure stored in an electronic medium.

* **contest**.  A single race in an election, for example a race for a
  position like Governor or Mayor or a non-candidate race like a ballot
  measure.  A contest can have multiple winners like in the case of
  at-large School Board race for multiple seats.

* **exhausted vote**.  A vote counting towards no candidate and that
  (1) is not an overvote, and (2) did count towards a candidate in a previous
  round.

* **overvote**.  A vote counting towards no candidate because the
  voter marked more than the allowed number of candidates.

* **physical vote**.  The physical or electronic markings that contain a
  voter's selections cast for a single contest in an election.  For example,
  in the case of a "vote for one" contest, a vote could be a bubbled-in
  oval or, in the case of a vote for a write-in candidate, a bubbled-in
  oval in conjunction with a hand-written name.  In the case of an RCV
  contest, a vote would be the collection of markings indicating a voter's
  first, second, and third choices, etc.

* **round**.  A sequential stage of the vote tabulation for an RCV contest.

* **undervote**.  A vote counting towards no candidate and that is
  (1) not an overvote, and (2) did not count towards a candidate in a
  previous round.

* **vote**.  The information capturing a voter's selections for a particular
  contest after the marks in the corresponding physical vote have been
  interpreted as references to particular candidates or choices.  In this
  sense, the input to a vote tabulation algorithm are the "votes" rather
  than the "physical votes."


[DRE_voting_machine]: https://en.wikipedia.org/wiki/DRE_voting_machine
[SF_Charter_13_102_a]: ../statutes/san_francisco.txt#L11
