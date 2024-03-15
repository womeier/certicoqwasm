#!/usr/bin/env python3

files = ["vs.v", "Binom.v", "sha256.v"]

for file in files:
	lines = open(file).read().split("\n")

	should_count = True

	count = 0
	for l in lines:
		if "Qed" in l or "Defined" in l or "Admitted" in l:
			should_count = True
		if "Lemma" in l or "Theorem" in l:
			should_count = False
		count += int(should_count)

	print(f"{file}: {count}")
