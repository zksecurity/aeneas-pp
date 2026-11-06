module
public import Aeneas.Std.Core.Core
public section

namespace Aeneas.Std

@[rust_trait "core::borrow::Borrow"]
structure core.borrow.Borrow (Self : Type _) (Borrowed : Type _) where
  borrow : Self → Result Borrowed

end Aeneas.Std
