# TO_USER

- **Loop stuck in DAG phase (5 iters)**: `archon loop` has re-invoked the DAG agent 5 times (iters 003–006) despite `DAG_STATUS.md` showing `Status: COMPLETE` since iter-002. The blueprint is done. Check the loop's COMPLETE-stop condition or manually trigger the plan phase (`archon loop --start-plan` or equivalent) to advance to P0 prover work.
- **Kudla 1997 §4 needed for P1**: `lem:fourier-coeff-factorization` in `Overview.tex` cites Kudla (1997) §4 for the Euler product factorization `E_T = |ω_X|^{-n²/2} ∏_v W_{T,v}`. This paper is not in `references/`. Supply the PDF or a DOI so the reference-retriever can fetch it before P1 prover work begins.
