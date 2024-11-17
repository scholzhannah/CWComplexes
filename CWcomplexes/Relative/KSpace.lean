import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.RestrictGen

open Set.Notation Topology

/-!
# Kspaces and the k-ification

In this file we will define k-spaces and the k-ification and prove basic properties about them.

## Main definitions
* `KSpace`: A k-space is a topological space in which a set `A` is open iff for every compact set
  `B`, the intersection `A ∩ B` is open in `B`.
* `instkification`: For a topological space `X` one can define another topology on `X` as follows:
  `A` is open iff for all compact sets `B`, the intersection `A ∩ B` is open in `B`.

## Main results
* `kspace_of_WeaklyLocallyCompactSpace`: every weakly locally compact space is a k-space
* `kspace_of_SequentialSpace`: every sequential space is a k-space
* `isCompact_iff_isCompact_in_kification`: The compact sets of a topological space and its
  k-ification agree.
* `kspace_kification`: The k-ification makes any space into a k-space.
* `kification_kspace_eq_self`: The k-ification of a k-space `X` preserves the topology on `X`.
* `continuous_kification_of_continuousOn_compact`: A map going to the k-ification of a topological
  space `X` is continuous if map going to `X` is continuous when restricted to every compact set.

## References
* [J. Munkres, *Topology*]
* <https://en.wikipedia.org/wiki/Compactly_generated_space>
-/

noncomputable section

/-! ### K-spaces-/


-- see `Topology.RestrictGenTopology.isCompact_of_weaklyLocallyCompact` and
--  `Topology.RestrictGenTopology.isCompact_of_seq`
