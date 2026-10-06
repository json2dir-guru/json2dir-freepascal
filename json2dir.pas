{ json2dir: create the directory tree a JSON document describes, in the current directory.
  Implements RFC J2D-1. Free Pascal, RTL only (System, BaseUnix, Syscall), hand-written JSON parser. }
program json2dir;

{$mode objfpc}{$H+}

uses
  BaseUnix, Syscall;

const
  O_NOFOLLOW_ = &400000; { Linux x86_64 }

type
  TKind = (nkObj, nkStr, nkLink, nkScript);
  PNode = ^TNode;
  TNode = record
    kind: TKind;
    s: AnsiString;                  { file content or link target }
    names: array of AnsiString;     { object members }
    vals: array of PNode;
  end;

var
  inp: AnsiString;
  p: SizeInt;

procedure Fail(const msg: AnsiString);
begin
  WriteLn(StdErr, 'json2dir: ', msg);
  Halt(1);
end;

{ ---------- input ---------- }

function ReadAll: AnsiString;
var
  buf: array[0..65535] of Char;
  n: TSsize;
  len: SizeInt;
begin
  Result := '';
  len := 0;
  repeat
    n := fpRead(0, buf, SizeOf(buf));
    if n < 0 then Fail('cannot read standard input');
    if n > 0 then
    begin
      SetLength(Result, len + n);
      Move(buf, Result[len + 1], n);
      Inc(len, n);
    end;
  until n = 0;
end;

procedure CheckUtf8(const s: AnsiString);
var
  i, n, need: SizeInt;
  c: Byte;
  cp, min: LongWord;
begin
  i := 1;
  n := Length(s);
  while i <= n do
  begin
    c := Byte(s[i]);
    if c < $80 then begin Inc(i); Continue; end
    else if (c and $E0) = $C0 then begin need := 1; cp := c and $1F; min := $80; end
    else if (c and $F0) = $E0 then begin need := 2; cp := c and $0F; min := $800; end
    else if (c and $F8) = $F0 then begin need := 3; cp := c and $07; min := $10000; end
    else Fail('input is not valid UTF-8');
    if i + need > n then Fail('input is not valid UTF-8');
    while need > 0 do
    begin
      Inc(i);
      c := Byte(s[i]);
      if (c and $C0) <> $80 then Fail('input is not valid UTF-8');
      cp := (cp shl 6) or (c and $3F);
      Dec(need);
    end;
    if (cp < min) or (cp > $10FFFF) or ((cp >= $D800) and (cp <= $DFFF)) then
      Fail('input is not valid UTF-8');
    Inc(i);
  end;
end;

{ ---------- JSON parser ---------- }

procedure SkipWs;
begin
  while (p <= Length(inp)) and (inp[p] in [' ', #9, #10, #13]) do Inc(p);
end;

function Peek: Char;
begin
  if p <= Length(inp) then Result := inp[p] else Result := #0;
end;

procedure Expect(c: Char);
begin
  SkipWs;
  if (p > Length(inp)) or (inp[p] <> c) then Fail('input is not valid JSON: expected "' + c + '"');
  Inc(p);
end;

function Utf8Of(cp: LongWord): AnsiString;
begin
  if cp < $80 then Result := Chr(cp)
  else if cp < $800 then Result := Chr($C0 or (cp shr 6)) + Chr($80 or (cp and $3F))
  else if cp < $10000 then
    Result := Chr($E0 or (cp shr 12)) + Chr($80 or ((cp shr 6) and $3F)) + Chr($80 or (cp and $3F))
  else
    Result := Chr($F0 or (cp shr 18)) + Chr($80 or ((cp shr 12) and $3F)) +
              Chr($80 or ((cp shr 6) and $3F)) + Chr($80 or (cp and $3F));
end;

function Hex4: LongWord;
var
  i: Integer;
  c: Char;
begin
  Result := 0;
  for i := 1 to 4 do
  begin
    c := Peek;
    case c of
      '0'..'9': Result := Result * 16 + LongWord(Ord(c) - Ord('0'));
      'a'..'f': Result := Result * 16 + LongWord(Ord(c) - Ord('a') + 10);
      'A'..'F': Result := Result * 16 + LongWord(Ord(c) - Ord('A') + 10);
    else
      Fail('input is not valid JSON: bad \u escape');
    end;
    Inc(p);
  end;
end;

function ParseString: AnsiString;
var
  start: SizeInt;
  cp, lo: LongWord;
begin
  Expect('"');
  Result := '';
  while True do
  begin
    start := p;
    while (p <= Length(inp)) and not (inp[p] in ['"', '\', #0..#31]) do Inc(p);
    if p > start then Result := Result + Copy(inp, start, p - start);
    if p > Length(inp) then Fail('input is not valid JSON: unterminated string');
    case inp[p] of
      '"': begin Inc(p); Exit; end;
      '\':
        begin
          Inc(p);
          case Peek of
            '"': Result := Result + '"';
            '\': Result := Result + '\';
            '/': Result := Result + '/';
            'b': Result := Result + #8;
            'f': Result := Result + #12;
            'n': Result := Result + #10;
            'r': Result := Result + #13;
            't': Result := Result + #9;
            'u':
              begin
                Inc(p);
                cp := Hex4;
                if (cp >= $DC00) and (cp <= $DFFF) then Fail('string contains an unpaired surrogate');
                if (cp >= $D800) and (cp <= $DBFF) then
                begin
                  if (Peek <> '\') or (p + 1 > Length(inp)) or (inp[p + 1] <> 'u') then
                    Fail('string contains an unpaired surrogate');
                  Inc(p, 2);
                  lo := Hex4;
                  if (lo < $DC00) or (lo > $DFFF) then Fail('string contains an unpaired surrogate');
                  cp := $10000 + ((cp - $D800) shl 10) + (lo - $DC00);
                end;
                Result := Result + Utf8Of(cp);
                Continue; { Hex4 already advanced p }
              end;
          else
            Fail('input is not valid JSON: bad escape');
          end;
          Inc(p);
        end;
    else
      Fail('input is not valid JSON: control character in string');
    end;
  end;
end;

function ParseValue(depth: Integer): PNode; forward;

function ParseObject(depth: Integer): PNode;
var
  name: AnsiString;
  v: PNode;
  i, n: SizeInt;
  found: Boolean;
begin
  if depth > 10000 then Fail('document is nested too deeply');
  New(Result);
  Result^.kind := nkObj;
  Expect('{');
  SkipWs;
  if Peek = '}' then begin Inc(p); Exit; end;
  repeat
    SkipWs;
    if Peek <> '"' then Fail('input is not valid JSON: expected a member name');
    name := ParseString;
    if (name = '') or (name = '.') or (name = '..') or (Pos('/', name) > 0) or (Pos(#0, name) > 0) then
      Fail('invalid name "' + name + '"');
    Expect(':');
    v := ParseValue(depth + 1);
    { duplicate names: the last occurrence wins }
    found := False;
    n := Length(Result^.names);
    for i := 0 to n - 1 do
      if Result^.names[i] = name then begin Result^.vals[i] := v; found := True; Break; end;
    if not found then
    begin
      SetLength(Result^.names, n + 1);
      SetLength(Result^.vals, n + 1);
      Result^.names[n] := name;
      Result^.vals[n] := v;
    end;
    SkipWs;
    if Peek = ',' then begin Inc(p); Continue; end;
    if Peek = '}' then begin Inc(p); Exit; end;
    Fail('input is not valid JSON: expected "," or "}"');
  until False;
end;

function ParseArray: PNode;
const
  Shape = 'an array must be ["link", target] or ["script", content]';
var
  kind, payload: AnsiString;
begin
  Expect('[');
  SkipWs;
  if Peek <> '"' then Fail(Shape);
  kind := ParseString;
  SkipWs;
  if Peek <> ',' then Fail(Shape);
  Inc(p);
  SkipWs;
  if Peek <> '"' then Fail(Shape);
  payload := ParseString;
  SkipWs;
  if Peek <> ']' then Fail(Shape);
  Inc(p);
  New(Result);
  if kind = 'link' then
  begin
    if Pos(#0, payload) > 0 then Fail('a link target cannot contain NUL');
    Result^.kind := nkLink;
  end
  else if kind = 'script' then Result^.kind := nkScript
  else Fail('unknown array kind "' + kind + '"');
  Result^.s := payload;
end;

function ParseValue(depth: Integer): PNode;
begin
  Result := nil;
  SkipWs;
  case Peek of
    '{': Result := ParseObject(depth);
    '[': Result := ParseArray;
    '"':
      begin
        New(Result);
        Result^.kind := nkStr;
        Result^.s := ParseString;
      end;
    't', 'f', 'n', '-', '0'..'9': Fail('numbers, true, false and null are not allowed');
  else
    Fail('input is not valid JSON: unexpected character');
  end;
end;

{ ---------- file system ---------- }

procedure WriteFile(const path, content: AnsiString; executable: Boolean);
var
  fd: cint;
  off, n: SizeInt;
  st: Stat;
begin
  { O_EXCL + O_NOFOLLOW: never write through an entry that appeared after the unlink }
  fd := fpOpen(PChar(path), O_WRONLY or O_CREAT or O_EXCL or O_NOFOLLOW_, &666);
  if fd < 0 then Fail(path + ': cannot create file');
  off := 0;
  while off < Length(content) do
  begin
    n := fpWrite(fd, content[off + 1], Length(content) - off);
    if n <= 0 then Fail(path + ': write failed');
    Inc(off, n);
  end;
  if executable then
  begin
    if fpFStat(fd, st) <> 0 then Fail(path + ': fstat failed');
    { BaseUnix has no fchmod wrapper in 3.2.2, so call the syscall directly }
    if do_syscall(syscall_nr_fchmod, TSysParam(fd), TSysParam((st.st_mode and &7777) or &111)) <> 0 then Fail(path + ': chmod failed');
  end;
  fpClose(fd);
end;

procedure Apply(const dir: AnsiString; node: PNode);
var
  i: SizeInt;
  path: AnsiString;
  v: PNode;
  st: Stat;
  exists, isDir: Boolean;
begin
  for i := 0 to High(node^.names) do
  begin
    path := dir + '/' + node^.names[i];
    v := node^.vals[i];
    exists := fpLstat(PChar(path), st) = 0;
    if not exists and (fpgeterrno <> ESysENOENT) then Fail(path + ': cannot stat');
    isDir := exists and fpS_ISDIR(st.st_mode);
    if v^.kind = nkObj then
    begin
      if not isDir then
      begin
        if exists and (fpUnlink(PChar(path)) <> 0) then Fail(path + ': cannot remove');
        if fpMkdir(PChar(path), &777) <> 0 then Fail(path + ': cannot create directory');
      end;
      Apply(path, v);
    end
    else
    begin
      { a directory in the way of a non-object is an error; anything else is replaced }
      if isDir then Fail(path + ': a directory is in the way');
      if exists and (fpUnlink(PChar(path)) <> 0) then Fail(path + ': cannot remove');
      case v^.kind of
        nkStr: WriteFile(path, v^.s, False);
        nkScript: WriteFile(path, v^.s, True);
        nkLink: if fpSymlink(PChar(v^.s), PChar(path)) <> 0 then Fail(path + ': cannot create link');
      end;
    end;
  end;
end;

var
  root: PNode;
begin
  if ParamCount > 0 then
  begin
    WriteLn(StdErr, 'usage: json2dir < document.json');
    Halt(2);
  end;
  inp := ReadAll;
  CheckUtf8(inp);
  p := 1;
  if Copy(inp, 1, 3) = #$EF#$BB#$BF then p := 4; { ignore a leading BOM }
  SkipWs;
  if p > Length(inp) then Fail('input is not valid JSON: empty input');
  if Peek <> '{' then Fail('the root of the document must be an object');
  { the whole document is parsed and validated before anything is written }
  root := ParseValue(0);
  SkipWs;
  if p <= Length(inp) then Fail('input is not valid JSON: trailing data');
  Apply('.', root);
end.
