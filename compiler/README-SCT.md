- The implementations of poly1305 and chacha20 are in the sct-examples/*
  folder, in the ref/ sub-folder for the scalar versions, and avx2 sub-folders
  for the vectorized versions.

Speculative constant-time
--------------------------------------------------------------------
- To check if a program is SCT-F, simply run:
   jasminc -v4_weak FILENAME
  At the end you see a message.
  Example:
    ./jasminc -v4_weak sct-examples/poly1305/avx2/poly1305_safe_fence.japp
  print 
    dependency: C = { out inlen k in }
  This means that the variables "out", "inlen", "k", and "in" should be public.
  This is ok, because they are pointers (or length arguments) so there values are public,
  only the values pointed to are secret.

- Remember that you also need to perform the seculative-safety check to be sure 
  that the program is SCT.
  
Speculative safety analysis
--------------------------------------------------------------------

- To check the speculative safety of the implementations, simply run:
     - `$ bash ./spec-safety-check`
  Note that the analysis of some implementations can take a very long time
  (from a few minutes for the ref/Poly1305 implementations to several hours
  for the avx2/Chacha20 implementations).

- By default, 3 analyses are run in parallel (if you have more cores,
  simply set the `MAXJOBS` variable at the beginning of the script to
  a higher value).

- The intermediate state of the analysis and the final results of the
  analysis of implem.jazz are written into implem.jazz.res in the same
  directory.

  The final results of an analysis comprise a summary of all safety
	violations encountered during the analysis (if any), plus an
	over-approximation of all memory ranges where stores and writes
  took place. The user must then check that the inferred memory
	ranges are indeed the intended one. These inferred memory
	ranges can serve as a memory calling contract for the function.

  As an example, we give below the final results we obtained when
	analyzing ref/Poly1305_movcc. We explain how to interpret them below.
	(We also make a few important remarks at the end of the README).


Example of analysis results
--------------------------------------------------------------------

*** No Safety Violation

Memory ranges (standard semantics):
  mem_p.632: [0; 16]
  mem_inlen: [0; 0]
  mem_k: [0; 32]
  
Memory ranges (speculative semantics):
  mem_p.632: [0; 16]
  mem_inlen: [0; 0]
  mem_k: [0; 32]
  
[* Standard semantics *]
* Rel:
{inv_in ≥ 0, mem_in ≥ 0, inv_inlen ≥ mem_in,
 inv_inlen ≤ 18446744073709551615, inv_in ≤ 18446744073709551615}
mem_in ∊ [0; 18446744073709551615]

[* Speculative semantics (live) *]
* Rel:
{inv_in ≥ 0, mem_in ≥ 0, inv_inlen ≥ mem_in,
 inv_inlen ≤ 18446744073709551615, inv_in ≤ 18446744073709551615}
mem_in ∊ [0; 18446744073709551615]

[* Speculative semantics (dead) *]
* Rel:
{inv_in ≥ 0, mem_in ≥ 0, inv_inlen ≥ mem_in,
 inv_inlen ≤ 18446744073709551615, inv_in ≤ 18446744073709551615}
mem_in ∊ [0; 18446744073709551615]


Explanation
--------------------------------------------------------------------

- There are three sets of inferred memory ranges:
    - the ranges below [* Standard semantics *] are an over-approximation of
		the memory accesses done under the standard (non-speculative) semantics
		at the end of the program execution.
		
		- the ranges below [* Speculative semantics (live) *] are an
		over-approximation of the memory accesses done under the speculative
		semantics at the end of the program execution.

		- the ranges below [* Speculative semantics (dead) *] are an
		over-approximation of the memory accesses done under the speculative
		semantics during the program execution, and that were "killed" by a fence.
		Essentially, these memory accesses have taken place in branches of the
		execution that were stopped because the program miss-peculated.

- The complete memory ranges are simply the union of the memory ranges for all
  three sets.

- Note that some ranges are given using intervals:
    - e.g. `mem_k: [0; 32]` states that the pointer `k` (which points to the key)
		is 32 bytes long (the interval is misprinted, it inclusive on the left and
		exclusive on the right).

- Other ranges are given through conjunctions of linear inequalities.
    - e.g. the entry:
		* Rel:
    {inv_in ≥ 0,
		 mem_in ≥ 0,
		 inv_inlen ≥ mem_in,
		 inv_inlen ≤ 18446744073709551615,
		 inv_in ≤ 18446744073709551615}
    mem_in ∊ [0; 18446744073709551615]

    states that the memory accesses to the input pointer are done anywhere
		between 0 and `inv_inlen` (which is the initial value of the inlen variable).
		This can be rewritten as `0 ≤ mem_in ≤ inv_inlen`, which is exactly what we
		wanted.
		

A few remarks
--------------------------------------------------------------------

- There can be hundred of thousands of line of logs. Simply jump to
  the end of the `.res` file for the final results.

- The Chacha20 implementations are analysed twice, once to get bounds
  on memory access for the plaintext pointer `plain`, and once for the
	cipher-text pointer `output`.

- We do not analyse the original Jasmin program, but the Jasmin program
  produced by the compiler after all the main passes of the compiler have
	been done.
  (this is crucial, as these passes do not preserve speculative safety. Note
	that the the remaining compiler passes are speculative safety preserving.)
	This program is printed at the beginning of the log file.
	Note that the Jasmin compiler may rename reuse some variables names.
	E.g., in the example above, `p.632` comes from such a renaming, and
	is actually the output pointer (which is 16 bytes long).



