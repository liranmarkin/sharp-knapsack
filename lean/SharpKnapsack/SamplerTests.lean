/-
Build-time evaluation checks for the verified sampler: the mass functions
are executable, and on a concrete instance they evaluate to exactly the
proven uniform distribution. `lake build` fails if any of these break.
-/
import SharpKnapsack.SamplerArrays

-- instance S = [1, 2], capacity 2: solutions ∅, {1}, {2} → mass 1/3 each
#guard samplerMass [1, 2] 2 [false, false] = 1 / 3
#guard samplerMass [1, 2] 2 [true, false] = 1 / 3
#guard samplerMass [1, 2] 2 [false, true] = 1 / 3
#guard samplerMass [1, 2] 2 [true, true] = 0
-- total mass one over all masks
#guard ((allMasks 2).map (samplerMass [1, 2] 2)).sum = 1
-- pruning agrees with the unpruned sampler, computably
#guard splitMassP [1, 2, 3] 3 [true, false, false] = splitMass [1, 2, 3] 3 [true, false, false]
#guard splitMassP [1, 2, 3] 3 [false, true, false] = splitMass [1, 2, 3] 3 [false, true, false]
-- a 4-item instance: capacity 3, weights [1,1,2,3]: solutions have mass 1/countLe
#guard countLe [1, 1, 2, 3] 3 = 8
#guard samplerMass [1, 1, 2, 3] 3 [true, true, false, false] = 1 / 8
#guard samplerMass [1, 1, 2, 3] 3 [false, false, false, true] = 1 / 8
#guard samplerMass [1, 1, 2, 3] 3 [true, false, false, true] = 0
