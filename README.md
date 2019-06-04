# CS263_PL
## Topic: Semantic equivalence for programs with break and continue (support for, do while, while)
> You should first define a Hoare logic, a denotational semantics and a small step semantics for a programming language with break and continue. Then you need to prove the equivalence between small step semantics and denotational semantics. Also, you should prove the soundness theorem of Hoare logic.

## Some Notes

We add 'for' and 'do while' in the definition of semantic equivalence but not in the definition of hoaresound for we have no idea about whether we should support 'for' and 'do while' in both of them or just in semantic equivalence. If necessary, we will add it in later work.

## Files And What We Define

### Semantic Equivalence(With 'for' and 'do while')

* definition_of_abc.v

  > Definition of aexp, bexp, astep, bstep, aeval, beval, com and notations.

* definition_of_two_semantics.v

  > Definition of two semantics, some lemmas that maybe useful and multi_steps. Some lemmas are proved, some are not yet. If we find it that the lemma is useful when we are proving the problem, then we will move it to the prove file and prove it. If not ,we will delete it.

* proving_equivalence_of_semantics.v

  > - Some lemmas we may use to prove the equivalence of semantics
  > - The equivalence proof goal: from line 1851.



### Hoare Sound(Without 'for' and 'do while')

* Imp8.v

  > Most of it is the same with the Imp8.v that we download from [Programming Languages](http://jhc.sjtu.edu.cn/public/courses/CS263/) web. We change something to add break and continue:
  >
  > - Definition of com: from line 54 to line 61.
  > - Notation of com: from line 64 to line 75.
  > - Definition of ceval: from line 214 to line 223.
  > - Definition of cstep: from line 529 to line 639.
  > - Defintion of hoare prove rules: from line 1235 to line 1277.
  > - Defintion of provable: from line 1850 to line 1877

* hoare_sound.v

  > Definition of hoaresound, some useful lemma and Hoare_logic_soundness, which is exact what we need to prove.

### Contributer

- [Jiabin Fang](https://github.com/Bagusutar)
- [Xiao Li](https://github.com/shjdlx)
- [Chenyu Yang](https://github.com/Achronferry)
- [Zihan Xu](https://github.com/madcpt)
- [Yi Kuang](https://github.com/Schemeer)

