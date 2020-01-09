import java.io.IOException;

import java.nio.file.Files;
import java.nio.file.FileSystems;

public class RH1190835 {

  public static void main(String[] args) throws IOException {

    if (args.length == 0)
      {
	System.err.println("Please specify a Java file to test.");
	System.exit(-1);
      }
    
    // Check NIO file type detection
    System.out.println("Checking type of this file is returned as text/x-java...");
    String fType = Files.probeContentType(FileSystems.getDefault().getPath(args[0]));
    if (!"text/x-java".equals(fType))
      {
	System.out.println("File type detection failed; returned " + fType);
	System.exit(-1);
      }
    System.out.println("Correct file type returned: " + fType);
  }

}
