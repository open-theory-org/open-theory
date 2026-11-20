Library	Targets	Status
gradient-descent-lean	4.28	Test build failed (Fréchet/gradient simp API changed)
Optlib	4.13	Far too old to build here
FoML, StatLean, SLT	4.29–4.32	Couldn't be required whole. We copied in small, patched subsets (with their source recorded) and build those as our own libraries
SciLean, Tyr	4.28 / 4.29	Also need native code (LeanBLAS, LibTorch)
TensorLib	4.33	Uses a different tensor type from TorchLean's. Mixing them means writing conversions
lean4-mlir, Arlib, ProbabilityApproximation, ArtificialTheorems, NeuralNetworkProofs	various	Source read; compatibility not checked yet