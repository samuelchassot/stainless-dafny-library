module ISBN {
  datatype Option<T> = 
    None
  | Some(t: T)

  function get<T>(o: Option<T>): T
    requires o != None
  {
    match o {
      case Some(t) => t
    }
  }

  datatype UnvalidatedISBN10 = 
    ISBN10(domain: seq<int>, editor: seq<int>, publication: seq<int>, checksum: int)
  
  datatype ValidatedISBN10 = 
    ISBN10(isbn: UnvalidatedISBN10)


  function validateISBN10Gallimard(isbn: UnvalidatedISBN10): (res: Option<ValidatedISBN10>)
    ensures match res 
      {
        case None => true
        case Some(v) => isISBN10Valid(isbn) && v.isbn == isbn
      }
  {
    if !isISBN10Valid(isbn) || isbn.domain != [2] 
      || (isbn.editor != [7, 4, 2, 4] && isbn.editor != [0, 7]) then None()
    else
      var r := Some(ValidatedISBN10.ISBN10(isbn));
      r

  }
  function isbn10RangeValid(isbn: UnvalidatedISBN10): bool 

  {
    |isbn.domain| + |isbn.editor| + |isbn.publication| == 9 &&
    0 <= isbn.checksum && isbn.checksum <= 10 &&
    (forall x: int | 0 <= x < |isbn.domain| :: 0 <= isbn.domain[x] <= 9) &&
    (forall x: int | 0 <= x < |isbn.editor| :: 0 <= isbn.editor[x] <= 9) &&
    (forall x: int | 0 <= x < |isbn.publication| :: 0 <= isbn.publication[x] <= 9)
  }

  function weightedSum(xs: seq<int>, i: int, acc: int): int
  {
    if |xs| == 0 then acc
    else weightedSum(xs[1..], i - 1, acc + xs[0] * i)
  }

  function isISBN10Valid(isbn: UnvalidatedISBN10): bool
  {
    isbn10RangeValid(isbn) && errCode(isbn) == isbn.checksum
  }
  
  function errCode(isbn: UnvalidatedISBN10): int
  {
    var domSum := weightedSum(isbn.domain, 10, 0);
    var edSum := weightedSum(isbn.editor, 10 - |isbn.editor|, 0);
    var pubSum := weightedSum(isbn.publication, 10 - |isbn.editor|, 0);

    var r1: int := (domSum + edSum + pubSum) % 11;
    if r1 == 0 then 0 else 11 - r1
  }

}