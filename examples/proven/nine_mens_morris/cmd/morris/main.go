package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"

	morris "github.com/frederik-jatzkowski/go-lean/examples/proven/nine_mens_morris"
)

func main() {
	state := morris.Start()
	input := bufio.NewScanner(os.Stdin)
	fmt.Println("Nine Men's Morris. Enter point numbers, or q to quit.")
	for {
		show(func(point uint) byte {
			switch state.Board().At(point) {
			case morris.White:
				return 'W'
			case morris.Black:
				return 'B'
			default:
				return '.'
			}
		})
		switch state.Outcome() {
		case morris.WhiteWins:
			fmt.Println("White wins.")
			return
		case morris.BlackWins:
			fmt.Println("Black wins.")
			return
		case morris.Draw:
			fmt.Printf("Draw after %d moves without a capture.\n", morris.DrawAfter)
			return
		}

		player := "White"
		if state.Turn() == morris.Black {
			player = "Black"
		}
		want := 1
		switch {
		case state.Pending():
			fmt.Printf("%s, capture (point): ", player)
		case state.Placing():
			fmt.Printf("%s, place (point): ", player)
		default:
			fmt.Printf("%s, move (from to): ", player)
			want = 2
		}
		if !input.Scan() {
			if err := input.Err(); err != nil {
				fmt.Fprintln(os.Stderr, err)
			}
			return
		}
		fields := strings.Fields(input.Text())
		if len(fields) == 1 && strings.EqualFold(fields[0], "q") {
			return
		}
		if len(fields) != want {
			fmt.Println("Enter the requested point numbers.")
			continue
		}
		points, ok := parsePoints(fields)
		if !ok {
			fmt.Println("Point numbers are 0 through 23.")
			continue
		}

		var accepted bool
		switch {
		case state.Pending():
			state, accepted = unpack(state.Capture(points[0]))
		case state.Placing():
			state, accepted = unpack(state.Place(points[0]))
		default:
			state, accepted = unpack(state.Move(points[0], points[1]))
		}
		if !accepted {
			fmt.Println("Illegal action. Try again.")
		}
	}
}

func parsePoints(fields []string) ([]uint, bool) {
	points := make([]uint, len(fields))
	for i, field := range fields {
		number, err := strconv.ParseUint(field, 10, 8)
		if err != nil || number >= morris.Points {
			return nil, false
		}
		points[i] = uint(number)
	}
	return points, true
}

func show(mark func(uint) byte) {
	cell := func(point uint) string {
		return fmt.Sprintf("%02d%c", point, mark(point))
	}
	fmt.Printf(`
%s------------%s------------%s
 |              |              |
 |   %s-------%s-------%s   |
 |    |         |         |    |
 |    |   %s--%s--%s   |    |
 |    |    |         |    |    |
%s--%s--%s       %s--%s--%s
 |    |    |         |    |    |
 |    |   %s--%s--%s   |    |
 |    |         |         |    |
 |   %s-------%s-------%s   |
 |              |              |
%s------------%s------------%s
`, cell(0), cell(1), cell(2),
		cell(8), cell(9), cell(10),
		cell(16), cell(17), cell(18),
		cell(7), cell(15), cell(23), cell(19), cell(11), cell(3),
		cell(22), cell(21), cell(20),
		cell(14), cell(13), cell(12),
		cell(6), cell(5), cell(4))
}

func unpack[T any](result interface {
	Next() T
	Accepted() bool
}) (T, bool) {
	return result.Next(), result.Accepted()
}
