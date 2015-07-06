Glossary
========

This document is a convenient guide to the meaning of various election
terms as we use them throughout this project.

These definitions should be taken as _informative_ rather than normative.
The normative definitions are spelled out elsewhere in the project using
a formal language.  Nevertheless, the definitions here are consistent with
and descriptive of the normative definitions.  Also, as much as possible,
we choose names in the formalized parts of this project (e.g. function
names, variable names, etc) to be consistent with this glossary.

Note that the statutes of individual jurisdictions may assign different
meanings to these terms.  For example, in the first sentence of
[Section 13.102.a][SF_Charter_13_102_a] of the San Francisco Charter,
the Charter uses "ballot" as meaning "vote" in the sense of this glossary.
For this reason, the project strives to
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
  can be a data structure stored in an electronic medium, like a region
  of memory in a memory cartridge.

* **candidate**.  A person running for a particular contest.

* **contest**.  A single race in an election, for example a race for a
  position like Governor or Mayor or a yes-no race like a ballot measure.
  A contest can have multiple winners like in the case of an at-large School
  Board race for multiple seats.

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

* **undervote**.  A vote counting towards no candidate and that
  (1) is not an overvote, and (2) did not count towards a candidate in a
  previous round.

* **vote**.  The information capturing a voter's selections for a particular
  contest after the marks in the corresponding physical vote have been
  interpreted as references to particular candidates or choices.  For
  example, a ballot scanner may be responsible for converting physical votes
  to votes, and a post-election audit may be responsible for ensuring that
  this was done correctly.  Additionally, it is typically the votes rather
  than the physical votes that serve as the input to vote tabulation
  algorithm or software (e.g. as in this project).


[DRE_voting_machine]: https://en.wikipedia.org/wiki/DRE_voting_machine
[SF_Charter_13_102_a]: ../statutes/san_francisco.txt#L11
