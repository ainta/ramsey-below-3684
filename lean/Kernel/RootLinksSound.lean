import Kernel.RootLinks.C0000
import Kernel.RootLinks.C0001
import Kernel.RootLinks.C0002
import Kernel.RootLinks.C0003
import Kernel.RootLinks.C0004
import Kernel.RootLinks.C0005
import Kernel.RootLinks.C0006
import Kernel.RootLinks.C0007
import Kernel.RootLinks.C0008
import Kernel.RootLinks.C0009
import Kernel.RootLinks.C0010
import Kernel.RootLinks.C0011
import Kernel.RootLinks.C0012
import Kernel.RootLinks.C0013
import Kernel.RootLinks.C0014
import Kernel.RootLinks.C0015
import Kernel.RootLinks.C0016
import Kernel.RootLinks.C0017
import Kernel.RootLinks.C0018
import Kernel.RootLinks.C0019
import Kernel.RootLinks.C0020
import Kernel.RootLinks.C0021
import Kernel.RootLinks.C0022
import Kernel.RootLinks.C0023
import Kernel.RootLinks.C0024
import Kernel.RootLinks.C0025
import Kernel.RootLinks.C0026
import Kernel.RootLinks.C0027
import Kernel.RootLinks.C0028
import Kernel.RootLinks.C0029
import Kernel.RootLinks.C0030
import Kernel.RootLinks.C0031
import Kernel.RootLinks.C0032
import Kernel.RootLinks.C0033
import Kernel.RootLinks.C0034
import Kernel.RootLinks.C0035
import Kernel.RootLinks.C0036
import Kernel.RootLinks.C0037
import Kernel.RootLinks.C0038
import Kernel.RootLinks.C0039
namespace Compact3684.ReflectedRoot
theorem all_checked (i : Nat) (hi : i ≤ Reflected.R00.last) : guard i = true := by
  change i ≤ 19999 at hi
  by_cases h0 : i < 10240
  ·
    by_cases h1 : i < 5120
    ·
      by_cases h2 : i < 2560
      ·
        by_cases h3 : i < 1024
        ·
          by_cases h4 : i < 512
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0000.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0001.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 1536
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0002.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 2048
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0003.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0004.checked (by omega) (by omega)
      ·
        by_cases h3 : i < 3584
        ·
          by_cases h4 : i < 3072
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0005.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0006.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 4096
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0007.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 4608
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0008.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0009.checked (by omega) (by omega)
    ·
      by_cases h2 : i < 7680
      ·
        by_cases h3 : i < 6144
        ·
          by_cases h4 : i < 5632
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0010.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0011.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 6656
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0012.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 7168
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0013.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0014.checked (by omega) (by omega)
      ·
        by_cases h3 : i < 8704
        ·
          by_cases h4 : i < 8192
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0015.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0016.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 9216
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0017.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 9728
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0018.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0019.checked (by omega) (by omega)
  ·
    by_cases h1 : i < 15360
    ·
      by_cases h2 : i < 12800
      ·
        by_cases h3 : i < 11264
        ·
          by_cases h4 : i < 10752
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0020.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0021.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 11776
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0022.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 12288
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0023.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0024.checked (by omega) (by omega)
      ·
        by_cases h3 : i < 13824
        ·
          by_cases h4 : i < 13312
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0025.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0026.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 14336
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0027.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 14848
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0028.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0029.checked (by omega) (by omega)
    ·
      by_cases h2 : i < 17920
      ·
        by_cases h3 : i < 16384
        ·
          by_cases h4 : i < 15872
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0030.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0031.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 16896
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0032.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 17408
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0033.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0034.checked (by omega) (by omega)
      ·
        by_cases h3 : i < 18944
        ·
          by_cases h4 : i < 18432
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0035.checked (by omega) (by omega)
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0036.checked (by omega) (by omega)
        ·
          by_cases h4 : i < 19456
          ·
            exact checkedRange_at Compact3684.ReflectedRoot.C0037.checked (by omega) (by omega)
          ·
            by_cases h5 : i < 19968
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0038.checked (by omega) (by omega)
            ·
              exact checkedRange_at Compact3684.ReflectedRoot.C0039.checked (by omega) (by omega)
#print axioms all_checked
end Compact3684.ReflectedRoot
