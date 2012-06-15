package frontend;

public interface TreeProvider {
  public ProgramTree tree() throws CompileException;
}