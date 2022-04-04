library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity adder_tb is
  generic (N : integer := 5);
end entity;

architecture behavioural of adder_tb is
  component adder is
    port(
      ext_0 : in std_logic_vector (N-1 downto 0);
      ext_1 : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N downto 0)
      );
  end component;

  signal a,b : unsigned (N-1 downto 0);
  signal c : unsigned (N downto 0);
  constant A_MAX : integer := 2**(a'length)-1;
  constant B_MAX : integer := 2**(b'length)-1;

begin

  uut : adder port map(
    ext_0 =>std_logic_vector(a),
    ext_1 =>std_logic_vector(b),
    unsigned(res) => c);

  process is
  begin
    for i in 0 to A_MAX loop
      for j in 0 to B_MAX loop
        a <= to_unsigned(i,a'length);
        b <= to_unsigned(j,b'length);
        wait for 2 ns;
        assert (std_logic_vector(c) = std_logic_vector(to_unsigned(i+j,c'length)))
          report "error" severity failure;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
