# CS263_PL
## Topic: Semantic equivalence for programs with break and continue (support for, do while, while)
> You should first define a Hoare logic, a denotational semantics and a small step semantics for a programming language with break and continue. Then you need to prove the equivalence between small step semantics and denotational semantics. Also, you should prove the soundness theorem of Hoare logic.

## Files And What We Define

### Semantic Equivalence

* definition_of_abc.v

  > Definition of aexp, bexp, astep, bstep, aeval, beval, com and notations.

* definition_of_two_semantics.v

  > Definition of two semantics, some lemmas that maybe useful and multi_steps. Some lemmas are proved, some are not yet. If we find it that the lemma is useful when we are proving the problem, then we will move it to the prove file and prove it. If not ,we will delete it.

* proving_equivalence_of_semantics.v

  > - Some lemmas we may use to prove the equivalence of semantics
  > - The equivalence proof goal: from line 1851.



### Hoare Sound

* Imp8.v

  > Most of it is the same with the Imp8.v that we download from [Programming Languages](http://jhc.sjtu.edu.cn/public/courses/CS263/) web. But there are still something di:
  >
  > - Definition of com: from line 54 to line 63.
  > - Notation of com: from line 66 to line 81.
  > - Definition of ceval: from line 145 to line 284.
  > - Definition of cstep: from line 590 to line 743.
  > - Defintion of hoare prove rules: from line 1347 to line 1287.
  > - Defintion of provable: from line 1962 to line 1995

* hoare_sound.v

  > - Definition of hoaresound: from line 11 to 14
  > - Some useful lemma: from line 16 to line 181
  > - Hoare_logic_soundness: from line 211.

### Contributer

- [Jiabin Fang](https://github.com/Bagusutar)
- [Xiao Li](https://github.com/shjdlx)
- [Chenyu Yang](https://github.com/Achronferry)
- [Zihan Xu](https://github.com/madcpt)
- [Yi Kuang](https://github.com/Schemeer)

