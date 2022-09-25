library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity id_tb is
  generic (N : integer := 1);
end entity;

architecture behavioural of id_tb is
  component id is
    port(
      xs : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N-1 downto 0)
      );
  end component;

  signal a,b : unsigned (N-1 downto 0);
  constant A_MAX : integer := 2**(a'length)-1;

begin

  uut : id port map(
    xs =>std_logic_vector(a),
    unsigned(res) => b);

  process is
  begin
    for i in 0 to A_MAX loop
        a <= to_unsigned(i,a'length);
        wait for 2 ns;
        assert (std_logic_vector(b) = std_logic_vector(a))
          report "error" severity failure;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
