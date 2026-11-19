package transpile

import (
	"bytes"
	"fmt"
	"maps"
	"regexp"
	"slices"
	"strings"

	"github.com/pelletier/go-toml/v2"
)

const (
	beginRoots = "# BEGIN go-lean managed roots"
	endRoots   = "# END go-lean managed roots"
)

type managedRoots struct {
	start, end int
	indent     string
	newline    string
	manual     map[string]bool
	generated  []string
}

type rootMarker struct {
	start, end int
	line       int
	indent     string
	newline    string
	begin      bool
}

var rootsMarkerLine = regexp.MustCompile(`(?m)^([^\r\n]*)(# (?:BEGIN|END) go-lean managed roots)[ \t]*(\r?\n|$)`)

func parseManagedRoots(data []byte) (map[int]managedRoots, error) {
	// Replace reserved comment lines with unique array entries in a temporary
	// copy. The TOML decoder then tells us which roots array owns each marker.
	markers := make(map[string]rootMarker)
	var probe strings.Builder
	cursor := 0
	for _, match := range rootsMarkerLine.FindAllSubmatchIndex(data, -1) {
		start, end := match[0], match[1]
		indent := string(data[match[2]:match[3]])
		tag := string(data[match[4]:match[5]])
		line := bytes.Count(data[:start], []byte{'\n'}) + 1
		if strings.Trim(indent, " \t") != "" {
			return nil, fmt.Errorf("line %d: go-lean markers must be on their own lines", line)
		}
		token := fmt.Sprintf("__go_lean_marker_%d__", line)
		for bytes.Contains(data, []byte(token)) {
			token += "_"
		}
		newline := string(data[match[6]:match[7]])
		markers[token] = rootMarker{start, end, line, indent, newline, tag == beginRoots}
		probe.Write(data[cursor:start])
		fmt.Fprintf(&probe, "%q,\n", token)
		cursor = end
	}
	if len(markers) == 0 {
		return nil, nil
	}
	probe.Write(data[cursor:])
	var config struct {
		Libraries []struct{ Roots any } `toml:"lean_lib"`
	}
	if err := toml.Unmarshal([]byte(probe.String()), &config); err != nil {
		return nil, fmt.Errorf("invalid TOML in managed roots: go-lean markers must be inside a lean_lib roots array with commas between entries: %w", err)
	}

	blocks := make(map[int]managedRoots)
	for i, lib := range config.Libraries {
		roots, _ := lib.Roots.([]any)
		block := managedRoots{manual: make(map[string]bool)}
		stringsOnly := true
		for _, root := range roots {
			name, ok := root.(string)
			if !ok {
				stringsOnly = false
				continue
			}
			marker, found := markers[name]
			if !found {
				if block.start == 0 || block.end != 0 {
					block.manual[name] = true
				} else {
					block.generated = append(block.generated, name)
				}
				continue
			}
			delete(markers, name)
			switch {
			case marker.begin && block.start == 0:
				block.start, block.indent, block.newline = marker.end, marker.indent, marker.newline
			case !marker.begin && block.start != 0 && block.end == 0:
				block.end = marker.start
			default:
				return nil, fmt.Errorf("line %d: expected one BEGIN marker followed by one END marker per roots array", marker.line)
			}
		}
		if block.start == 0 {
			continue
		}
		if block.end == 0 {
			return nil, fmt.Errorf("line %d: missing END go-lean managed roots marker", bytes.Count(data[:block.start], []byte{'\n'}))
		}
		if !stringsOnly {
			return nil, fmt.Errorf("line %d: managed roots array must contain only module name strings", bytes.Count(data[:block.start], []byte{'\n'}))
		}
		blocks[i] = block
	}
	for _, marker := range markers {
		return nil, fmt.Errorf("line %d: go-lean markers must be inside a lean_lib roots array", marker.line)
	}
	return blocks, nil
}

// lakeRoot escapes path components that Lean's name parser cannot read as
// ordinary identifiers, including dots within a component and numeric names.
func lakeRoot(path string) string {
	parts := strings.Split(path, "/")
	for i, part := range parts {
		if !plainIdentifier(part) {
			parts[i] = "«" + part + "»"
		}
	}
	return strings.Join(parts, ".")
}

func plainIdentifier(part string) bool {
	for i, ch := range part {
		if ch != '_' && !(ch >= 'a' && ch <= 'z') && !(ch >= 'A' && ch <= 'Z') &&
			!(i > 0 && (ch >= '0' && ch <= '9' || ch == '\'')) {
			return false
		}
	}
	return part != ""
}

func updateManagedRoots(data []byte, blocks map[int]managedRoots, names map[int]map[string]bool) ([]byte, error) {
	var result bytes.Buffer
	cursor := 0
	for _, i := range slices.Sorted(maps.Keys(blocks)) {
		block := blocks[i]
		result.Write(data[cursor:block.start])
		for _, name := range slices.Sorted(maps.Keys(names[i])) {
			if block.manual[name] {
				continue
			}
			encoded, err := toml.Marshal(struct{ Root string }{name})
			if err != nil {
				return nil, err
			}
			_, value, _ := bytes.Cut(bytes.TrimRight(encoded, "\n"), []byte(" = "))
			result.WriteString(block.indent)
			result.Write(value)
			result.WriteByte(',')
			result.WriteString(block.newline)
		}
		cursor = block.end
	}
	result.Write(data[cursor:])
	return result.Bytes(), nil
}
