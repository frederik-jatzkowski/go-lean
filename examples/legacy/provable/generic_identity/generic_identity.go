package generic_identity

//golean:verify identityPreservesValue : ∀ {α : Type} (value : α),
//golean:verify+   Identity value = value
func Identity[T any](value T) T { return value }
