package worker

//golean:assume preservesInput : ∀ x : Int64,
//golean:assume+ Mirror x = x
//golean:assume preservesZero : Mirror 0 = 0
func Mirror(x int64) int64 {
	result := make(chan int64)
	go func() { result <- x }()
	return <-result
}
