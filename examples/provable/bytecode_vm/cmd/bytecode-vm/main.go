package main

import (
	"fmt"

	vm "github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm"
)

func main() {
	program := [8]byte{vm.OpIncrement, vm.OpIncrement, vm.OpHalt}
	state, status := vm.Run(program)
	if status != vm.Halted {
		fmt.Printf("VM stopped with status %d\n", status)
		return
	}
	fmt.Printf("Accumulator = %d\n", state.Accumulator)
}
