import CertDefs.Defs

namespace Rotation.Cert

theorem cert67 : check67 = true := by native_decide

theorem cert345 : check345 = true := by native_decide

theorem overlap_check : checkOverlap 3 = true ∧ checkOverlap 4 = true ∧ checkOverlap 5 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem recurrence_check : checkRecurrence 3 8 = true ∧ checkRecurrence 4 8 = true := by
  constructor <;> native_decide

theorem factorization_check :
    (perms (List.range 3)).all (checkFactorization · 8) = true ∧
    (perms (List.range 4)).all (checkFactorization · 8) = true := by
  constructor <;> native_decide

end Rotation.Cert
