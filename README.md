# Rocq LLM Benchmarks

A Rocq LLM benchmark that is mutating. It is meant to help check if the LLM actually learned the underlying reasoning or just memorized previous benchmarks.

## Todo

$$LLMs := \{ Llama,\ ChatGPT,\ Deepseek,\ Claude \}$$
1. Gather a set of normal Coq/Rocq benchmarks. These should be put into `./benchmarks/`
2. Establish a harness for running a given benchmark on: $LLMs$ (probably [Ollama](https://ollama.com/))
   1. In particular, this should have interface like `Run : Coq_File -> LLM_Name -> (Proven Correctly : Bool, Proven Time : float)`
3. Establish a `mutator` which will **rename primitive inductive constructors**, and **apply theorem rewriting** to make an equivalent but differently formulated theorem. 
   Interface like `Mutate : Coq_File -> Change_Ind : bool -> Thm_Rew : bool -> Coq_File`
4. Test each of the $LLMs$:
   1. Test the provability of the original theorem. $\forall b \in benchmarks,\forall l \in LLMs,\ Run\ b\ l$
   2. Test the provability of a mutated theorem. $\forall b \in benchmarks,\forall l \in LLMs,\ Run\ (mutate\ b\ true\ true)\ l$
5. Compare results from the above testing

## Notes

The dataset of .v files in coq_projects has been sourced from the [CoqGym](https://github.com/princeton-vl/CoqGym) project.
