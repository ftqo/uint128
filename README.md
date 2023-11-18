# uint128

[![GoDoc](https://godoc.org/github.com/ftqo/uint128?status.svg)](https://godoc.org/github.com/ftqo/uint128)

`uint128` is a fork of `github.com/lukechampine/uint128`. If you want a properly
tested codebase, go use that one. This fork implements `sql.Scanner` instead of
`fmt.Scanner`, along with implementing `encoding.BinaryMarshaler` and 
`encoding.TextMarshaler`. Some panics were removed in favor of error handling

```
go get github.com/ftqo/uint128
```
