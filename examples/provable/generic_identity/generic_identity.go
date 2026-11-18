package generic_identity

//golean:verify
func Identity[T any](value T) T { return value }
