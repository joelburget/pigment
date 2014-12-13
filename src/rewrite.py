from glob import glob

def replace_birdtracks(contents):
    """Replace lines of concurrent birdtracks with a code environment.

    > codes
    > codes

    becomes

    \\begin{code}
    codes
    codes
    \\end{code}
    """

    new_lst = []
    in_block = False

    for i in range(len(contents)):
        line = contents[i]
        now_in = line.startswith("> ")
        if now_in:
            push_me = line[2:]
        elif line == ">\n":
            push_me = "\n"
        else:
            push_me = line
        begin_block = not in_block and now_in

        # out -> in
        if begin_block:
            in_block = True
            new_lst.append("\\begin{code}\n")

        new_lst.append(push_me)

        # in -> out
        if in_block and not now_in:
            in_block = False
            new_lst[-1] = "\\end{code}\n"

        # last line, in block
        elif in_block and i == len(contents) - 1:
            new_lst.append("\\end{code}\n")

    return new_lst

def merge_sections(contents):
    """Merge code sections separated by only space.

        \\begin{code}
        code
        \\end{code}

        \\begin{code}
        code
        \\end{code}

    becomes

        \\begin{code}
        code

        code
        \\end{code}
    """

    new_lst = []
    last_out = None
    on_notice = False

    for i in range(len(contents)):
        line = contents[i]
        transition_in = line == "\\begin{code}\n"
        transition_out = line == "\\end{code}\n"

        if transition_out:
            on_notice = True
            last_out = len(new_lst)

        new_lst.append(line)

        if transition_in:
            if on_notice:
                del new_lst[last_out]
                del new_lst[-1]

        if line != "" and not transition_out:
            on_notice = False

    return new_lst

test_f = open("Main.lhs", "rw")

if __name__ == "__main__":
    for name in glob("*.lhs") + glob("*/*.lhs") + glob("*/*/*.lhs"):
        print "rewriting " + name
        f = open(name, "r+")
        write_me = "".join(merge_sections(replace_birdtracks(f.readlines())))
        f.seek(0)
        f.write(write_me)
        f.truncate()
        f.close()
