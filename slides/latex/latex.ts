/** A tiny LaTeX-to-HTML renderer. */

enum Atom {
  None = -1,
  Ord = 0,
  Op = 1,
  Bin = 2,
  Rel = 3,
  Open = 4,
  Close = 5,
  Punct = 6,
  Inner = 7,
}

enum Space {
  Thin = "\u2009",
  Regular = " ",
  ThreePerEm = " ",
  FourPerEm = " ",
  SixPerEm = " ",
}

type Substitution = [Atom, string | null];

const Substitutions: Record<string, Substitution> = {
  "eps": [Atom.Ord, "<i>ϵ</i>"],
  "Theta": [Atom.Ord, "Θ"],
  "theta": [Atom.Ord, "θ"],
  "lambda": [Atom.Ord, "λ"],
  "Omega": [Atom.Ord, "Ω"],
  "omega": [Atom.Ord, "ω"],
  "field": [Atom.Ord, "𝔽"],
  "reals": [Atom.Ord, "ℝ"],
  "integers": [Atom.Ord, "ℤ"],
  "infty": [Atom.Ord, "∞"],
  "\\|": [Atom.Ord, "‖"],
  "delta": [Atom.Ord, "<i>δ</i>"],
  "Delta": [Atom.Ord, "<i>Δ</i>"],
  "mu": [Atom.Ord, "<i>μ</i>"],

  "log": [Atom.Op, null],
  "mod": [Atom.Op, null],

  "times": [Atom.Bin, "×"],
  "*": [Atom.Bin, "<span class=laasx>*</span>"],
  "+": [Atom.Bin, "+"],
  "/": [Atom.Bin, "<span class=ladiv>/</span>"],
  "-": [Atom.Bin, "<span class=lamns>−</span>"],
  "cdot": [Atom.Bin, "·"],
  "neq": [Atom.Bin, "≠"],

  "=": [Atom.Rel, "<span class=laeq>=</span>"],
  "le": [Atom.Rel, "≤"],
  "ge": [Atom.Rel, "≥"],
  "to": [Atom.Rel, "<span class=lato>→</span>"],
  "mapsto": [Atom.Rel, "<span class=lamt>↦</span>"],
  "in": [Atom.Rel, "<span class=lain>∈</span>"],

  "langle": [Atom.Open, "<span class=laal>⟨</span>"],
  "lVert": [Atom.Open, "‖"],
  "\\{": [Atom.Open, "<span class=lacl>{</span>"],
  "(": [Atom.Open, "<span class=lapl>(</span>"],
  "[": [Atom.Open, "<span class=lasl>[</span>"],

  "rangle": [Atom.Close, "<span class=laar>⟩</span>"],
  "rVert": [Atom.Close, "‖"],
  "\\}": [Atom.Close, "<span class=lacr>}</span>"],
  ")": [Atom.Close, "<span class=lapr>)</span>"],
  "]": [Atom.Close, "<span class=lasr>]</span>"],

  ",": [Atom.Punct, ","],
  "colon": [Atom.Punct, ":"],

  "ldots": [Atom.Inner, "…"],
  "quad": [Atom.Inner, "  "],
};

/** TeXbook, p. 170. */
const SpaceTable: number[][] = [
  [0, 1, 2, 3, 0, 0, 0, 1],
  [1, 1, 9, 3, 0, 0, 0, 1],
  [2, 2, 9, 9, 2, 9, 9, 2],
  [3, 3, 9, 0, 3, 0, 0, 3],
  [0, 0, 9, 0, 0, 0, 0, 0],
  [0, 1, 2, 3, 0, 0, 0, 1],
  [1, 1, 9, 1, 1, 1, 1, 1],
  [1, 1, 2, 3, 1, 0, 1, 1],
];

const Alpha = /[a-zA-Z]*/;
const Digits = /[0-9]*/;
const RightAttachment = /[a-zA-Z._’\-,]*/;
const LeftAttachment = /[a-zA-Z.\-]*$/;

const getSpace = (leftAtom: Atom, rightAtom: Atom): string => {
  if (leftAtom == Atom.None || rightAtom == Atom.None)
    return "";

  const spaceType = SpaceTable[leftAtom][rightAtom];
  if (spaceType == 0)
    return "";
  return spaceType == 3 ? Space.ThreePerEm : Space.Regular;
};

type Argument = { content: string; end: number };

/** Read a braced argument, keeping nested groups and escaped braces intact. */
const readGroup = (tex: string, start: number): Argument | null => {
  while (start < tex.length && /\s/.test(tex.charAt(start)))
    start++;
  if (tex.charAt(start) != "{")
    return null;

  let depth = 1;
  for (let i = start + 1; i < tex.length; i++) {
    const character = tex.charAt(i);
    if (character == "\\") {
      i++;
    } else if (character == "{") {
      depth++;
    } else if (character == "}" && --depth == 0) {
      return { content: tex.slice(start + 1, i), end: i + 1 };
    }
  }
  return null;
};

const readScript = (tex: string, start: number): Argument =>
  readGroup(tex, start) || { content: tex.charAt(start), end: start + 1 };

/** Render the contents of one inline formula. */
const renderInline = (
  tex: string,
  leftAttachment: string | null,
  rightAttachment: string | null,
): string => {
  const baseMode = leftAttachment != null;
  const length = tex.length;
  let output = "";
  let lastAtom = Atom.None;

  for (let i = 0; i < length;) {
    const code = tex.charCodeAt(i);
    const character = tex.charAt(i);
    i++;

    if (code == "\\".charCodeAt(0)) {
      const commandMatch = tex.slice(i).match(Alpha);
      let command = commandMatch == null ? "" : commandMatch[0];
      if (command.length == 0) {
        command = tex.slice(i - 1, i + 1);
        i++;
      } else {
        i += command.length;
      }

      if (command == "muti" || command == "tsmuti") {
        const left = readGroup(tex, i);
        const right = left && readGroup(tex, left.end);
        if (left && right) {
          const informationSymbol = command == "tsmuti"
            ? "<span class=laover><b class=labf>I</b></span>"
            : "<b class=labf>I</b>";
          const separator = command == "tsmuti" ? ";" : ":";
          output += getSpace(lastAtom, Atom.Op) +
            informationSymbol + "<span class=lapl>(</span>" +
            renderInline(left.content, null, null) +
            "<span class=lacolon>" + separator + "</span>" +
            renderInline(right.content, null, null) +
            "<span class=lapr>)</span>";
          lastAtom = Atom.Close;
          i = right.end;
          continue;
        }
      }

      if (command == "emid") {
        output += Space.Thin + "|" + Space.Thin;
        lastAtom = Atom.Ord;
        continue;
      }

      if (command == "frac") {
        const numerator = readGroup(tex, i);
        const denominator = numerator && readGroup(tex, numerator.end);
        if (numerator && denominator) {
          output += getSpace(lastAtom, Atom.Inner) +
            "<span class=lafrac><span class=lafrac-num>" +
            renderInline(numerator.content, null, null) +
            "</span><span class=lafrac-den>" +
            renderInline(denominator.content, null, null) +
            "</span></span>";
          lastAtom = Atom.Inner;
          i = denominator.end;
          continue;
        }
      }

      if (command == "bar" || command == "mathrm") {
        const argument = readGroup(tex, i);
        if (argument) {
          output += getSpace(lastAtom, Atom.Ord) +
            "<span class=" + (command == "bar" ? "laover" : "laroman") + ">" +
            renderInline(argument.content, null, null) + "</span>";
          lastAtom = Atom.Ord;
          i = argument.end;
          continue;
        }
      }

      const substitution = Substitutions[command];
      if (substitution) {
        output += getSpace(lastAtom, substitution[0]);
        output += substitution[1] == null
          ? "<span class=laop>" + command + "</span>"
          : substitution[1];
        lastAtom = substitution[0];
      }
    } else if (code == "^".charCodeAt(0)) {
      const { content: superscript, end } = readScript(tex, i);
      i = end;
      output += "<sup class=lasup>" +
        renderInline(superscript, null, null) + "</sup>";
    } else if (code == "_".charCodeAt(0)) {
      const { content: subscript, end } = readScript(tex, i);
      i = end;

      if (tex.charCodeAt(i) == "^".charCodeAt(0)) {
        i++;
        const { content: superscript, end } = readScript(tex, i);
        i = end;
        output += "<span class=lasupsub><sup class=lassup>" +
          renderInline(superscript, null, null) +
          "</sup><br><sub class=lassub>" +
          renderInline(subscript, null, null) + "</sub></span>";
      } else {
        output += "<sub class=lasub>" +
          renderInline(subscript, null, null) + "</sub>";
      }
    } else if (
      "0".charCodeAt(0) <= code && code <= "9".charCodeAt(0)
    ) {
      const numberMatch = tex.slice(i).match(Digits);
      const rest = numberMatch == null ? "" : numberMatch[0];
      i += rest.length;
      output += getSpace(lastAtom, Atom.Ord) + character + rest;
      lastAtom = Atom.Ord;
    } else if (code != " ".charCodeAt(0)) {
      const substitution = Substitutions[character];
      if (substitution) {
        const atom = substitution[0];
        if (baseMode && atom == Atom.Rel) {
          const smallLeftHandSide = i < 3;
          return "<span class=law>" + leftAttachment + output +
            getSpace(lastAtom, Atom.Rel) +
            (smallLeftHandSide ? "" : "</span><span class=law>") +
            substitution[1] + getSpace(lastAtom, Atom.Rel) + "</span>" +
            renderInline(tex.slice(i), "", rightAttachment);
        }
        output += getSpace(lastAtom, atom) + substitution[1];
        lastAtom = atom;
      } else {
        output += getSpace(lastAtom, Atom.Ord) +
          "<i>" + character + "</i>";
        lastAtom = Atom.Ord;
      }
    }
  }

  if (
    !baseMode ||
    (leftAttachment == "" && rightAttachment == "" && output.length < 9)
  )
    return output;
  return "<span class=law>" + leftAttachment + output +
    rightAttachment + "</span>";
};

/** Render all inline and display formulas in an HTML fragment. */
const renderParagraph = (source: string): string => {
  let paragraph = source;
  const blocks = paragraph.split("$$");
  if (blocks.length % 2 == 0)
    return paragraph;

  for (let i = 1; i < blocks.length; i += 2) {
    blocks[i] = "<div class=laeqn><div class=laeqni>" +
      renderInline(blocks[i], null, null) + "</div></div>";
  }
  paragraph = blocks.join("");

  const parts = paragraph.split("$");
  if (parts.length % 2 == 0)
    return paragraph;

  for (let i = 1; i < parts.length; i += 2) {
    const leftMatch = parts[i - 1].match(LeftAttachment);
    const rightMatch = parts[i + 1].match(RightAttachment);
    const left = leftMatch == null ? "" : leftMatch[0];
    const right = rightMatch == null ? "" : rightMatch[0];

    if (left.length > 0)
      parts[i - 1] = parts[i - 1].slice(0, -left.length);
    parts[i + 1] = parts[i + 1].slice(right.length);
    parts[i] = renderInline(parts[i], left, right);

    if (left == "" && parts[i - 1].length > 0) {
      parts[i - 1] = parts[i - 1].replace(/\s+$/, "") +
        Space.FourPerEm;
    }
    if (right == "" && parts[i + 1].length > 0) {
      parts[i + 1] = Space.FourPerEm +
        parts[i + 1].replace(/^\s+/, "");
    }
  }
  return parts.join("");
};

const renderElement = (element: Element): void => {
  element.innerHTML = renderParagraph(element.innerHTML);
};

export { renderElement, renderInline, renderParagraph };
