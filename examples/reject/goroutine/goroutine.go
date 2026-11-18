//go:build golean_reject

package goroutine

//golean:verify
func Relay(value int64) int64 {
	out := make(chan int64, 1)
	go func() { out <- value }()
	return <-out
}
