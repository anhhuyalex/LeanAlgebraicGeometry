import AlgebraicJacobian.Cohomology.FlatBaseChange
import AlgebraicJacobian.Cohomology.FlatBaseChangeGlobal
import AlgebraicJacobian.Cohomology.RegroupHelper
import AlgebraicJacobian.Cohomology.SheafCompose
import AlgebraicJacobian.Cohomology.StructureSheafAb
import AlgebraicJacobian.Cohomology.StructureSheafModuleK
import AlgebraicJacobian.Cohomology.MayerVietorisCore
import AlgebraicJacobian.Cohomology.MayerVietorisCover
-- Čech-cohomology development merged from the Cech-Cohomology subproject
-- (enrich merge, 2026-06-18). Closes the formerly-orphaned CechNerve / Rⁱf_*
-- Čech lane: pushPullFunctor + pushPullMap_comp + cech_computes_higherDirectImage.
import AlgebraicJacobian.Cohomology.HigherDirectImage
import AlgebraicJacobian.Cohomology.HigherDirectImagePresheaf
import AlgebraicJacobian.Cohomology.CechHigherDirectImage
import AlgebraicJacobian.Cohomology.CechAcyclic
import AlgebraicJacobian.Cohomology.AcyclicResolution
import AlgebraicJacobian.Cohomology.PresheafCech
import AlgebraicJacobian.Cohomology.FreePresheafComplex
import AlgebraicJacobian.Cohomology.CechBridge
import AlgebraicJacobian.Cohomology.AbsoluteCohomology
import AlgebraicJacobian.Cohomology.CechToCohomology
import AlgebraicJacobian.Cohomology.TildeExactness
import AlgebraicJacobian.Cohomology.AffineSerreVanishing
import AlgebraicJacobian.Cohomology.QcohRestrictBasicOpen
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLeg
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid1
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid2
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegTop
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegAux
import AlgebraicJacobian.Cohomology.CechSectionIdentification
import AlgebraicJacobian.Cohomology.CechAugmentedResolution
import AlgebraicJacobian.Cohomology.OpenImmersionPushforward
import AlgebraicJacobian.Cohomology.CechTermAcyclic
import AlgebraicJacobian.Cohomology.CechToHigherDirectImage
import AlgebraicJacobian.Cohomology.ModulesCoverConservativity
-- Affine essential-image heart of the open-immersion Beck–Chevalley (Stacks 02KG)
import AlgebraicJacobian.Cohomology.AffinePushPullEssImage
-- Pullback of quasi-coherent modules along an arbitrary morphism (Stacks 01BG)
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
-- Target-local roadmap nodes preserved across the merge (unconditional Rⁱf_*
-- packaging + Čech flat base change, Stacks 02KH) — see file header.
import AlgebraicJacobian.Cohomology.CechHigherDirectImageUnconditional
import AlgebraicJacobian.Genus
import AlgebraicJacobian.RigidityLemma
import AlgebraicJacobian.Jacobian
import AlgebraicJacobian.AbelJacobi
import AlgebraicJacobian.Picard.RelativeSpec
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse
-- Comparison-iso substrate merged from the Line-Bundle-Comparison-Iso
-- subproject (T1 merge, 2026-07-02). Headline: exists_tensorObj_inverse
-- (the L ⊗ L⁻¹ ≅ O_C keystone) proved sorry-free in TensorObjInverse,
-- via the DUAL/D3′ route (PresheafDualPullback* + PullbackTensorMapIso +
-- TrivialisationRestrict). PullbackTensorComp.lean was retired in the
-- merge: its D3′ lemma set was absorbed into TensorObjSubstrate.lean
-- (proved), and its remaining helpers had no consumers.
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullback
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualUnitPullback
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullbackNatural
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorMapIso
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorIso
import AlgebraicJacobian.Picard.TensorObjSubstrate.TrivialisationRestrict
import AlgebraicJacobian.Picard.TensorObjInverse
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.GeometricallyConnectedSection
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.IdentityComponent
import AlgebraicJacobian.Picard.TangentSpaceDualNumbers
import AlgebraicJacobian.Picard.TangentSpaceSchemePoints
import AlgebraicJacobian.Picard.TangentSpaceStalkAlgebra
import AlgebraicJacobian.Picard.TangentSpaceIdentitySection
import AlgebraicJacobian.Picard.DualNumberUnits
import AlgebraicJacobian.Picard.Pic0AbelianVariety
import AlgebraicJacobian.Picard.FlatteningStratification
import AlgebraicJacobian.Picard.EntryIdeal
import AlgebraicJacobian.Picard.EntryIdealStratum
import AlgebraicJacobian.Picard.FlatteningStratificationUniversal
import AlgebraicJacobian.Picard.GenericFlatnessGeometric
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.QuotScheme
-- Grassmannian/Quot representability development merged from the
-- GR-quot_closure subproject (union merge, 2026-06-22). Headline:
-- AlgebraicGeometry.Grassmannian.represents (rank-d quotient functor
-- representability) + the section graded ring/module lane, all sorry-free.
import AlgebraicJacobian.Picard.GradedHilbertSerre
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.GrassmannianCells
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.Picard.QuotFunctorDef
import AlgebraicJacobian.Picard.GrassmannianRepresentability
import AlgebraicJacobian.Picard.LineBundleCoherence
import AlgebraicJacobian.RiemannRoch.WeilDivisor
import AlgebraicJacobian.Albanese.AlbaneseUP
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Albanese.CoheightBridge
import AlgebraicJacobian.Albanese.Thm32RationalMapExtension
