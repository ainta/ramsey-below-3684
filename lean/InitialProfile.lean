import InitialUniform
import Ramsey3683Bootstrap.Certificate
import Kernel.InitialTangents.C0000
import Kernel.InitialTangents.C0001
import Kernel.InitialTangents.C0002
import Kernel.InitialTangents.C0003
import Kernel.InitialTangents.C0004
import Kernel.InitialTangents.C0005
import Kernel.InitialTangents.C0006
import Kernel.InitialTangents.C0007
import Kernel.InitialTangents.C0008
import Kernel.InitialTangents.C0009
import Kernel.InitialTangents.C0010
import Kernel.InitialTangents.C0011
import Kernel.InitialTangents.C0012
import Kernel.InitialTangents.C0013
import Kernel.InitialTangents.C0014
import Kernel.InitialTangents.C0015
import Kernel.InitialTangents.C0016
import Kernel.InitialTangents.C0017
import Kernel.InitialTangents.C0018
import Kernel.InitialTangents.C0019
import Kernel.InitialTangents.C0020
import Kernel.InitialTangents.C0021
import Kernel.InitialTangents.C0022
import Kernel.InitialTangents.C0023
import Kernel.InitialTangents.C0024
import Kernel.InitialTangents.C0025
import Kernel.InitialTangents.C0026
import Kernel.InitialTangents.C0027
import Kernel.InitialTangents.C0028
import Kernel.InitialTangents.C0029
import Kernel.InitialTangents.C0030
import Kernel.InitialTangents.C0031
import Kernel.InitialTangents.C0032
import Kernel.InitialTangents.C0033
import Kernel.InitialTangents.C0034
import Kernel.InitialTangents.C0035
import Kernel.InitialTangents.C0036
import Kernel.InitialTangents.C0037
import Kernel.InitialTangents.C0038
import Kernel.InitialTangents.C0039
import Kernel.InitialTangents.C0040
import Kernel.InitialTangents.C0041
import Kernel.InitialTangents.C0042
import Kernel.InitialTangents.C0043
import Kernel.InitialTangents.C0044
import Kernel.InitialTangents.C0045
import Kernel.InitialTangents.C0046
import Kernel.InitialTangents.C0047
import Kernel.InitialTangents.C0048
import Kernel.InitialTangents.C0049
import Kernel.InitialTangents.C0050
import Kernel.InitialTangents.C0051
import Kernel.InitialTangents.C0052
import Kernel.InitialTangents.C0053
import Kernel.InitialTangents.C0054
import Kernel.InitialTangents.C0055
import Kernel.InitialTangents.C0056
import Kernel.InitialTangents.C0057
import Kernel.InitialTangents.C0058
import Kernel.InitialTangents.C0059
import Kernel.InitialTangents.C0060
import Kernel.InitialTangents.C0061
import Kernel.InitialTangents.C0062
import Kernel.InitialTangents.C0063
import Kernel.InitialTangents.C0064
import Kernel.InitialTangents.C0065
import Kernel.InitialTangents.C0066
import Kernel.InitialTangents.C0067
import Kernel.InitialTangents.C0068
import Kernel.InitialTangents.C0069
import Kernel.InitialTangents.C0070
import Kernel.InitialTangents.C0071
import Kernel.InitialTangents.C0072
import Kernel.InitialTangents.C0073
import Kernel.InitialTangents.C0074
import Kernel.InitialTangents.C0075
import Kernel.InitialTangents.C0076
import Kernel.InitialTangents.C0077
import Kernel.InitialTangents.C0078
namespace Compact3684.InitialProfile
open RamseyLean Ramsey3683Bootstrap Elementary
def chunks : List InitialChunk := [
InitialChunk.mk 256 Compact3684.InitialTangents.C0000.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0001.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0002.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0003.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0004.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0005.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0006.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0007.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0008.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0009.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0010.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0011.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0012.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0013.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0014.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0015.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0016.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0017.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0018.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0019.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0020.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0021.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0022.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0023.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0024.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0025.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0026.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0027.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0028.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0029.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0030.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0031.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0032.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0033.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0034.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0035.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0036.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0037.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0038.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0039.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0040.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0041.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0042.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0043.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0044.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0045.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0046.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0047.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0048.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0049.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0050.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0051.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0052.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0053.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0054.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0055.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0056.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0057.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0058.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0059.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0060.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0061.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0062.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0063.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0064.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0065.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0066.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0067.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0068.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0069.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0070.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0071.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0072.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0073.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0074.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0075.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0076.payload,
InitialChunk.mk 256 Compact3684.InitialTangents.C0077.payload,
InitialChunk.mk 32 Compact3684.InitialTangents.C0078.payload]
theorem chunks_checked : chunks.all InitialChunk.guard = true := by
  simp only [chunks, List.all_cons, List.all_nil, InitialChunk.guard, Compact3684.InitialTangents.C0000.checked, Compact3684.InitialTangents.C0001.checked, Compact3684.InitialTangents.C0002.checked, Compact3684.InitialTangents.C0003.checked, Compact3684.InitialTangents.C0004.checked, Compact3684.InitialTangents.C0005.checked, Compact3684.InitialTangents.C0006.checked, Compact3684.InitialTangents.C0007.checked, Compact3684.InitialTangents.C0008.checked, Compact3684.InitialTangents.C0009.checked, Compact3684.InitialTangents.C0010.checked, Compact3684.InitialTangents.C0011.checked, Compact3684.InitialTangents.C0012.checked, Compact3684.InitialTangents.C0013.checked, Compact3684.InitialTangents.C0014.checked, Compact3684.InitialTangents.C0015.checked, Compact3684.InitialTangents.C0016.checked, Compact3684.InitialTangents.C0017.checked, Compact3684.InitialTangents.C0018.checked, Compact3684.InitialTangents.C0019.checked, Compact3684.InitialTangents.C0020.checked, Compact3684.InitialTangents.C0021.checked, Compact3684.InitialTangents.C0022.checked, Compact3684.InitialTangents.C0023.checked, Compact3684.InitialTangents.C0024.checked, Compact3684.InitialTangents.C0025.checked, Compact3684.InitialTangents.C0026.checked, Compact3684.InitialTangents.C0027.checked, Compact3684.InitialTangents.C0028.checked, Compact3684.InitialTangents.C0029.checked, Compact3684.InitialTangents.C0030.checked, Compact3684.InitialTangents.C0031.checked, Compact3684.InitialTangents.C0032.checked, Compact3684.InitialTangents.C0033.checked, Compact3684.InitialTangents.C0034.checked, Compact3684.InitialTangents.C0035.checked, Compact3684.InitialTangents.C0036.checked, Compact3684.InitialTangents.C0037.checked, Compact3684.InitialTangents.C0038.checked, Compact3684.InitialTangents.C0039.checked, Compact3684.InitialTangents.C0040.checked, Compact3684.InitialTangents.C0041.checked, Compact3684.InitialTangents.C0042.checked, Compact3684.InitialTangents.C0043.checked, Compact3684.InitialTangents.C0044.checked, Compact3684.InitialTangents.C0045.checked, Compact3684.InitialTangents.C0046.checked, Compact3684.InitialTangents.C0047.checked, Compact3684.InitialTangents.C0048.checked, Compact3684.InitialTangents.C0049.checked, Compact3684.InitialTangents.C0050.checked, Compact3684.InitialTangents.C0051.checked, Compact3684.InitialTangents.C0052.checked, Compact3684.InitialTangents.C0053.checked, Compact3684.InitialTangents.C0054.checked, Compact3684.InitialTangents.C0055.checked, Compact3684.InitialTangents.C0056.checked, Compact3684.InitialTangents.C0057.checked, Compact3684.InitialTangents.C0058.checked, Compact3684.InitialTangents.C0059.checked, Compact3684.InitialTangents.C0060.checked, Compact3684.InitialTangents.C0061.checked, Compact3684.InitialTangents.C0062.checked, Compact3684.InitialTangents.C0063.checked, Compact3684.InitialTangents.C0064.checked, Compact3684.InitialTangents.C0065.checked, Compact3684.InitialTangents.C0066.checked, Compact3684.InitialTangents.C0067.checked, Compact3684.InitialTangents.C0068.checked, Compact3684.InitialTangents.C0069.checked, Compact3684.InitialTangents.C0070.checked, Compact3684.InitialTangents.C0071.checked, Compact3684.InitialTangents.C0072.checked, Compact3684.InitialTangents.C0073.checked, Compact3684.InitialTangents.C0074.checked, Compact3684.InitialTangents.C0075.checked, Compact3684.InitialTangents.C0076.checked, Compact3684.InitialTangents.C0077.checked, Compact3684.InitialTangents.C0078.checked, show decide (0 < (32 : Nat)) = true by decide, show decide (0 < (256 : Nat)) = true by decide, Bool.and_self]
theorem chunks_length : chunks.length = 79 := by rfl
def chunkAt (i : Fin 79) : InitialChunk := chunks[i.val]'(by rw [chunks_length]; exact i.isLt)
theorem chunkAt_checked (i : Fin 79) : (chunkAt i).guard = true := by
  exact List.all_eq_true.mp chunks_checked _ (List.getElem_mem _)
abbrev Index := Fin 79 × Fin 256
noncomputable def lines (i : Index) : AffineLine := (chunkAt i.1).line i.2.val
noncomputable def profile : ℝ → ℝ := affineProfile lines
theorem valid : UniformRamseyExpBound profile := by
  apply Ramsey3683Bootstrap.UniformRamseyExpBound.affine_minimum lines
  intro i
  exact Compact3684.initial_uniform.weakenRate ((InitialChunk.sound (chunkAt_checked i.1) i.2.val).2.2)
theorem positive (i : Index) : 0 < (lines i).intercept ∧ 0 < (lines i).slope := by
  have h := InitialChunk.sound (chunkAt_checked i.1) i.2.val
  exact ⟨h.1,h.2.1⟩
#print axioms valid
end Compact3684.InitialProfile
