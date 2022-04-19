library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity mul13_tb is
  generic (N : integer := 5);
end entity;

architecture behavioural of mul13_tb is
  component mul13 is
    port(
      ext_0 : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N+4 downto 0)
      );
  end component;

  signal a : unsigned (N-1 downto 0);
  signal c : unsigned (N+4 downto 0);
  constant A_MAX : integer := 2**(a'length)-1;

begin

  uut : mul13 port map(
    ext_0 =>std_logic_vector(a),
    unsigned(res) => c);

  process is
  begin
    for i in 0 to A_MAX loop
      a <= to_unsigned(i,a'length);
      wait for 2 ns;
      assert (std_logic_vector(c) = std_logic_vector(to_unsigned(i*13,c'length)))
        report "error" severity failure;
    end loop;
    wait;
  end process;

end behavioural;
