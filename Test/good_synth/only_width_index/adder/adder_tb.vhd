library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity adder_tb is
  generic (NA : integer := 2;
           NB : integer := 3);
end entity;

architecture behavioural of adder_tb is
  component adder is
    port(
      xs : in std_logic_vector (NA-1 downto 0);
      ys : in std_logic_vector (NB-1 downto 0);
      res : out std_logic_vector (NB downto 0)
      );
  end component;

  signal a : unsigned (NA-1 downto 0);
  signal b : unsigned (NB-1 downto 0);
  signal c : unsigned (NB downto 0);
  constant A_MAX : integer := 2**(a'length)-1;
  constant B_MAX : integer := 2**(b'length)-1;

begin

  uut : adder port map(
    xs =>std_logic_vector(a),
    ys =>std_logic_vector(b),
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
