Formal RCV
==========

The purpose of this project is to make available formal specifications of
[ranked choice voting][rcv] (RCV), also known as [instant runoff voting][irv]
(IRV) in the case of a single winner and the [single transferable vote][stv]
(STV) more generally.

The focus will initially be on those variants of RCV used in US
jurisdictions.  The project will also aim to formalize ways of auditing RCV
elections.

The project will use [Coq][coq] for the formalization.

This work will inform the work of IEEE's Voting System Standards Committee
Working Group [VSSC 1622.6][vssc_1622_6] "Voting Methods Mathematical Models."


Jurisdiction Sources
--------------------

This section contains links to statutes and other sources that describe
the RCV rules in each jurisdiction we are interested in.

* Berkeley, CA: [Municipal Codes][berkeley_codes].
  See Charter, Article III, Sec. 5.12, "Use of instant runoff voting in lieu
  of runoff elections"; and Municipal Code, Title 2, Chapter 2.14,
  "Elections -- Instant Runoff Voting."
* Cambridge, MA
  * TODO
* Minneapolis, MN: [Code of Ordinances][minneapolis_codes].
  See Charter, Article III, Sec. 3.1; and Code of Ordinances, Title 8.5,
  Chapter 167, "Municipal Elections: Rules of Conduct."
* Oakland, CA
  * [Oakland Charter][oakland_charter] (See Article XI, Sec. 1105. Ranked
    Choice Voting.)
* Portland, ME
  * TODO
* San Francisco, CA
  * [SF Charter][sf_charter] (See Article XIII, Sec. 13.102. Instant Runoff
    Elections.)
* San Leandro, CA
  * TODO
* Saint Paul, MN
  * TODO


License
-------

The project is licensed under a BSD 3-Clause license.  See the
[LICENSE](LICENSE) file for details.


Contributors
------------

* Chris Jerdonek


[berkeley_codes]: http://codepublishing.com/ca/berkeley/
[coq]: https://coq.inria.fr/
[irv]: https://en.wikipedia.org/wiki/Instant-runoff_voting
[minneapolis_codes]: https://www.municode.com/library/mn/minneapolis/codes/code_of_ordinances?nodeId=11490
[oakland_charter]: https://www.municode.com/library/ca/oakland/codes/code_of_ordinances?nodeId=THCHOA
[rcv]: https://en.wikipedia.org/wiki/Ranked_Choice_Voting
[sf_charter]: http://www.amlegal.com/library/ca/sfrancisco.shtml
[stv]: https://en.wikipedia.org/wiki/Single_transferable_vote
[vssc_1622_6]: http://grouper.ieee.org/groups/1622/groups/6/index.html
