import Kernel.LogInterval
import Kernel.LogCatalog.C0000
import Kernel.LogCatalog.C0001
import Kernel.LogCatalog.C0002
import Kernel.LogCatalog.C0003
import Kernel.LogCatalog.C0004
import Kernel.LogCatalog.C0005
import Kernel.LogCatalog.C0006
import Kernel.LogCatalog.C0007
import Kernel.LogCatalog.C0008
import Kernel.LogCatalog.C0009
import Kernel.LogCatalog.C0010
import Kernel.LogCatalog.C0011
import Kernel.LogCatalog.C0012
import Kernel.LogCatalog.C0013
import Kernel.LogCatalog.C0014
import Kernel.LogCatalog.C0015
import Kernel.LogCatalog.C0016
import Kernel.LogCatalog.C0017
import Kernel.LogCatalog.C0018
import Kernel.LogCatalog.C0019
import Kernel.LogCatalog.C0020
import Kernel.LogCatalog.C0021
import Kernel.LogCatalog.C0022
import Kernel.LogCatalog.C0023
import Kernel.LogCatalog.C0024
import Kernel.LogCatalog.C0025
import Kernel.LogCatalog.C0026
import Kernel.LogCatalog.C0027
import Kernel.LogCatalog.C0028
import Kernel.LogCatalog.C0029
import Kernel.LogCatalog.C0030
import Kernel.LogCatalog.C0031
import Kernel.LogCatalog.C0032
import Kernel.LogCatalog.C0033
import Kernel.LogCatalog.C0034
import Kernel.LogCatalog.C0035
import Kernel.LogCatalog.C0036
import Kernel.LogCatalog.C0037
import Kernel.LogCatalog.C0038
import Kernel.LogCatalog.C0039
import Kernel.LogCatalog.C0040
import Kernel.LogCatalog.C0041
import Kernel.LogCatalog.C0042
import Kernel.LogCatalog.C0043
import Kernel.LogCatalog.C0044
import Kernel.LogCatalog.C0045
import Kernel.LogCatalog.C0046
import Kernel.LogCatalog.C0047
import Kernel.LogCatalog.C0048
import Kernel.LogCatalog.C0049
import Kernel.LogCatalog.C0050
import Kernel.LogCatalog.C0051
import Kernel.LogCatalog.C0052
import Kernel.LogCatalog.C0053
import Kernel.LogCatalog.C0054
import Kernel.LogCatalog.C0055
import Kernel.LogCatalog.C0056
import Kernel.LogCatalog.C0057
import Kernel.LogCatalog.C0058
import Kernel.LogCatalog.C0059
import Kernel.LogCatalog.C0060
import Kernel.LogCatalog.C0061
import Kernel.LogCatalog.C0062
import Kernel.LogCatalog.C0063
set_option maxRecDepth 100000
namespace Compact3684.Log18.AssembledCatalog
def chunks : List (List CatalogEntry) := [
Catalog.C0000.entries,
Catalog.C0001.entries,
Catalog.C0002.entries,
Catalog.C0003.entries,
Catalog.C0004.entries,
Catalog.C0005.entries,
Catalog.C0006.entries,
Catalog.C0007.entries,
Catalog.C0008.entries,
Catalog.C0009.entries,
Catalog.C0010.entries,
Catalog.C0011.entries,
Catalog.C0012.entries,
Catalog.C0013.entries,
Catalog.C0014.entries,
Catalog.C0015.entries,
Catalog.C0016.entries,
Catalog.C0017.entries,
Catalog.C0018.entries,
Catalog.C0019.entries,
Catalog.C0020.entries,
Catalog.C0021.entries,
Catalog.C0022.entries,
Catalog.C0023.entries,
Catalog.C0024.entries,
Catalog.C0025.entries,
Catalog.C0026.entries,
Catalog.C0027.entries,
Catalog.C0028.entries,
Catalog.C0029.entries,
Catalog.C0030.entries,
Catalog.C0031.entries,
Catalog.C0032.entries,
Catalog.C0033.entries,
Catalog.C0034.entries,
Catalog.C0035.entries,
Catalog.C0036.entries,
Catalog.C0037.entries,
Catalog.C0038.entries,
Catalog.C0039.entries,
Catalog.C0040.entries,
Catalog.C0041.entries,
Catalog.C0042.entries,
Catalog.C0043.entries,
Catalog.C0044.entries,
Catalog.C0045.entries,
Catalog.C0046.entries,
Catalog.C0047.entries,
Catalog.C0048.entries,
Catalog.C0049.entries,
Catalog.C0050.entries,
Catalog.C0051.entries,
Catalog.C0052.entries,
Catalog.C0053.entries,
Catalog.C0054.entries,
Catalog.C0055.entries,
Catalog.C0056.entries,
Catalog.C0057.entries,
Catalog.C0058.entries,
Catalog.C0059.entries,
Catalog.C0060.entries,
Catalog.C0061.entries,
Catalog.C0062.entries,
Catalog.C0063.entries]
theorem checked : chunks.all (fun entries => entries.all catalogGuard) = true := by
  simp only [chunks, List.all_cons, List.all_nil, Catalog.C0000.checked, Catalog.C0001.checked, Catalog.C0002.checked, Catalog.C0003.checked, Catalog.C0004.checked, Catalog.C0005.checked, Catalog.C0006.checked, Catalog.C0007.checked, Catalog.C0008.checked, Catalog.C0009.checked, Catalog.C0010.checked, Catalog.C0011.checked, Catalog.C0012.checked, Catalog.C0013.checked, Catalog.C0014.checked, Catalog.C0015.checked, Catalog.C0016.checked, Catalog.C0017.checked, Catalog.C0018.checked, Catalog.C0019.checked, Catalog.C0020.checked, Catalog.C0021.checked, Catalog.C0022.checked, Catalog.C0023.checked, Catalog.C0024.checked, Catalog.C0025.checked, Catalog.C0026.checked, Catalog.C0027.checked, Catalog.C0028.checked, Catalog.C0029.checked, Catalog.C0030.checked, Catalog.C0031.checked, Catalog.C0032.checked, Catalog.C0033.checked, Catalog.C0034.checked, Catalog.C0035.checked, Catalog.C0036.checked, Catalog.C0037.checked, Catalog.C0038.checked, Catalog.C0039.checked, Catalog.C0040.checked, Catalog.C0041.checked, Catalog.C0042.checked, Catalog.C0043.checked, Catalog.C0044.checked, Catalog.C0045.checked, Catalog.C0046.checked, Catalog.C0047.checked, Catalog.C0048.checked, Catalog.C0049.checked, Catalog.C0050.checked, Catalog.C0051.checked, Catalog.C0052.checked, Catalog.C0053.checked, Catalog.C0054.checked, Catalog.C0055.checked, Catalog.C0056.checked, Catalog.C0057.checked, Catalog.C0058.checked, Catalog.C0059.checked, Catalog.C0060.checked, Catalog.C0061.checked, Catalog.C0062.checked, Catalog.C0063.checked, Bool.and_self]
theorem sound : ∀ entries ∈ chunks, ∀ entry ∈ entries,
    Contains (entry.lo,entry.hi) (Real.log ((entry.argument : ℝ)/scale)) := by
  intro entries he
  exact catalogAll_sound entries (List.all_eq_true.mp checked entries he)
#print axioms sound
end Compact3684.Log18.AssembledCatalog
