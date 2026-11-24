package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"strings"

	game "github.com/frederik-jatzkowski/go-lean/examples/proven/grid_game"
)

func main() {
	wrap := flag.Bool("wrap", false, "wrap around the board edges")
	flag.Parse()

	input := bufio.NewScanner(os.Stdin)
	next := func() (game.Direction, bool) {
		for input.Scan() {
			switch strings.ToLower(strings.TrimSpace(input.Text())) {
			case "w":
				return game.Up, true
			case "s":
				return game.Down, true
			case "a":
				return game.Left, true
			case "d":
				return game.Right, true
			case "q":
				return 0, false
			default:
				fmt.Println("Enter w, a, s, d, or q.")
			}
		}
		return 0, false
	}

	fmt.Println("Move with W/A/S/D then Enter. Press Q then Enter to quit.")
	game.Play(*wrap, next, func(player game.Position) {
		for y := range uint8(game.Size) {
			for x := range uint8(game.Size) {
				cell := game.Position{X: x, Y: y}
				switch {
				case cell == player:
					fmt.Print("@")
				case game.Won(cell):
					fmt.Print("G")
				case game.IsWall(cell, *wrap):
					fmt.Print("#")
				default:
					fmt.Print(".")
				}
			}
			fmt.Println()
		}
		fmt.Println()
	})
	if err := input.Err(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
