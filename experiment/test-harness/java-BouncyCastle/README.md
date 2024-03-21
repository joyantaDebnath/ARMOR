### How to compile
Here is an example
```
javac -cp bcprov-jdk18on-171.jar:bcpkix-jdk18on-171.jar test_dn.java
```

### How to run
Here is an example
```
java -cp ":bcprov-jdk18on-171.jar:bcpkix-jdk18on-171.jar:." test_dn entity.pem example.com
```

### Important Note!!
Note that if the code is running on the Win/Mac, the ":" should be replaced to ";"