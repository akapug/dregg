/-
# Dregg2.Verify.ContractG — deprecated import path; production contracts live in `Verify/Contract`.
-/
import Dregg2.Verify.Contract

namespace Dregg2.Verify

abbrev GatedCellContract := Production.Contract
noncomputable abbrev ofCellContract := Production.liftFromKernelForest
noncomputable abbrev revokedPersistsG := revokedPersists
noncomputable abbrev logAppendOnlyG := logAppendOnly

end Dregg2.Verify